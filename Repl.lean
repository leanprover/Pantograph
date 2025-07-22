import Std.Data.HashMap
import Pantograph

namespace Pantograph.Repl

open Lean

structure Context where
  coreContext : Core.Context
  -- If true, the environment will change after running `CoreM`
  inheritEnv : Bool := false

/-- Stores state of the REPL -/
structure State where
  options : Protocol.Options := {}
  nextId : Nat := 0
  goalStates : Std.HashMap Nat GoalState := Std.HashMap.emptyWithCapacity

  env : Environment
  -- Parser state
  scope : Elab.Command.Scope := { header := "" }

/-- Main monad for executing commands -/
abbrev MainM := ReaderT Context $ StateRefT State IO
/-- Main with possible exception -/
abbrev EMainM := Protocol.FallibleT $ ReaderT Context $ StateRefT State IO
def getMainState : MainM State := get

instance : MonadEnv MainM where
  getEnv := return (← get).env
  modifyEnv f := modify fun s => { s with env := f s.env  }

def withInheritEnv [Monad m] [MonadWithReaderOf Context m] [MonadLift MainM m] { α } (z : m α) : m α := do
  withTheReader Context ({ · with inheritEnv := true }) z

def newGoalState (goalState : GoalState) : MainM Nat := do
  let state ← get
  let stateId := state.nextId
  set { state with
    goalStates := state.goalStates.insert stateId goalState,
    nextId := state.nextId + 1
  }
  return stateId

def runCoreM { α } (coreM : CoreM α) : EMainM α := do
  let scope := (← get).scope
  let options := (← get).options
  let cancelTk? ← match options.timeout with
    | 0 => pure .none
    | _ => .some <$> IO.CancelToken.new
  let coreCtx : Core.Context := {
    (← read).coreContext with
    currNamespace      := scope.currNamespace,
    openDecls          := scope.openDecls,
    options            := scope.opts,
    initHeartbeats     :=  ← IO.getNumHeartbeats,
    cancelTk?,
  }
  let coreState : Core.State := {
    env := (← get).env
  }
  -- Remap the coreM to capture every exception
  let coreM' : CoreM _ :=
    try
      Except.ok <$> coreM
    catch ex =>
      let desc ← ex.toMessageData.toString
      return Except.error ({ error := "exception", desc } : Protocol.InteractionError)
    finally
      for {msg, ..} in (← getTraceState).traces do
        IO.eprintln (← msg.format.toIO)
      resetTraceState
  if let .some token := cancelTk? then
    runCancelTokenWithTimeout token (timeout := .ofBitVec options.timeout)
  let (result, state') ← match ← (coreM'.run coreCtx coreState).toIO' with
    | Except.error (Exception.error _ msg)   => Protocol.throw $ { error := "core", desc := ← msg.toString }
    | Except.error (Exception.internal id _) => Protocol.throw $ { error := "internal", desc := (← id.getName).toString }
    | Except.ok a                            => pure a
  if (← read).inheritEnv && result matches .ok _ then
    setEnv state'.env
  liftExcept result

def runCoreM' { α } (coreM : Protocol.FallibleT CoreM α) : EMainM α := do
  liftExcept $ ← runCoreM coreM.run

def liftMetaM { α } (metaM : MetaM α): EMainM α :=
  runCoreM metaM.run'
def liftTermElabM { α } (termElabM : Elab.TermElabM α) (levelNames : List Name := [])
    : EMainM α := do
  let scope := (← get).scope
  let context := {
    errToSorry := false,
    isNoncomputableSection := scope.isNoncomputable,
  }
  let state := {
    levelNames := scope.levelNames ++ levelNames,
  }
  runCoreM $ termElabM.run' context state |>.run'

section Goal

def goal_tactic (args: Protocol.GoalTactic): EMainM Protocol.GoalTacticResult := do
  let state ← getMainState
  let .some goalState := state.goalStates[args.stateId]? |
    Protocol.throw $ Protocol.errorIndex s!"Invalid state index {args.stateId}"
  let unshielded := args.autoResume?.getD state.options.automaticMode
  let site ← match args.goalId?, unshielded with
    | .some goalId, true => do
      let .some goal := goalState.goals[goalId]? |
        Protocol.throw $ Protocol.errorIndex s!"Invalid goal index {goalId}"
      pure (.prefer goal)
    | .some goalId, false => do
      let .some goal := goalState.goals[goalId]? |
        Protocol.throw $ Protocol.errorIndex s!"Invalid goal index {goalId}"
      pure (.focus goal)
    | .none, true => pure .unfocus
    | .none, false => do
      let .some goal := goalState.mainGoal? |
        Protocol.throw $ Protocol.errorIndex s!"No goals to be solved"
      pure (.focus goal)
  let nextGoalState?: Except _ TacticResult ← liftTermElabM do
    -- NOTE: Should probably use a macro to handle this...
    match args.tactic?, args.mode?, args.expr?, args.have?, args.let?, args.draft?  with
    | .some tactic, .none, .none, .none, .none, .none => do
      pure $ Except.ok $ ← goalState.tryTactic site tactic
    | .none, .some mode, .none, .none, .none, .none => match mode with
      | "tactic" => do -- Exit from the current fragment
        pure $ Except.ok $ ← goalState.fragmentExit site
      | "conv" => do
        pure $ Except.ok $ ← goalState.convEnter site
      | "calc" => do
        pure $ Except.ok $ ← goalState.calcEnter site
      | _ => pure $ .error $ Protocol.errorOperation s!"Invalid mode {mode}"
    | .none, .none, .some expr, .none, .none, .none => do
      pure $ Except.ok $ ← goalState.tryAssign site expr
    | .none, .none, .none, .some type, .none, .none => do
      let binderName := args.binderName?.getD ""
      pure $ Except.ok $ ← goalState.tryHave site binderName type
    | .none, .none, .none, .none, .some type, .none => do
      let binderName := args.binderName?.getD ""
      pure $ Except.ok $ ← goalState.tryLet site binderName type
    | .none, .none, .none, .none, .none, .some draft => do
      pure $ Except.ok $ ← goalState.tryDraft site draft
    | _, _, _, _, _, _ =>
      pure $ .error $ Protocol.errorOperation
        "Exactly one of {tactic, mode, expr, have, let, draft} must be supplied"
  match nextGoalState? with
  | .error error => Protocol.throw error
  | .ok (.success nextGoalState messages) => do
    let env ← getEnv
    let nextStateId ← newGoalState nextGoalState
    let parentExprs := nextGoalState.parentExprs
    let hasSorry := parentExprs.any λ
      | .ok e => e.hasSorry
      | .error _ => false
    let hasUnsafe := parentExprs.any λ
      | .ok e => env.hasUnsafe e
      | .error _ => false
    let goals ← runCoreM $ nextGoalState.serializeGoals (options := state.options) |>.run'
    let messages ← messages.mapM (·.serialize)
    return {
      nextStateId? := .some nextStateId,
      goals? := .some goals,
      messages? := .some messages,
      hasSorry,
      hasUnsafe,
    }
  | .ok (.parseError message) =>
    return { messages? := .none, parseError? := .some message }
  | .ok (.invalidAction message) =>
    Protocol.throw $ errorI "invalid" message
  | .ok (.failure messages) =>
    let messages ← messages.mapM (·.serialize)
    return { messages? := .some messages }

end Goal

section Frontend

structure CompilationUnit where
  -- Environment immediately before the unit
  env : Environment
  boundary : Nat × Nat
  invocations : List Protocol.InvokedTactic
  sorrys : List Frontend.InfoWithContext
  messages : Array SerialMessage
  newConstants : NameSet

def frontend_process (args: Protocol.FrontendProcess): EMainM Protocol.FrontendProcessResult := do
  let options := (← getMainState).options
  let (fileName, file) ← match args.fileName?, args.file? with
    | .some fileName, .none => do
      let file ← IO.FS.readFile fileName
      pure (fileName, file)
    | .none, .some file =>
      pure ("<anonymous>", file)
    | _, _ => Protocol.throw $ errorI "arguments" "Exactly one of {fileName, file} must be supplied"
  let env?: Option Environment ← if args.readHeader then
      pure .none
    else do
      .some <$> getEnv
  let (context, state) ← do Frontend.createContextStateFromFile file fileName env? {}
  let frontendM: Frontend.FrontendM (List CompilationUnit) :=
    Frontend.mapCompilationSteps λ step => do
    let boundary := (step.src.startPos.byteIdx, step.src.stopPos.byteIdx)
    let invocations: Option (List Protocol.InvokedTactic) ← if args.invocations?.isSome then
        Frontend.collectTacticsFromCompilationStep step
      else
        pure []
    let sorrys ← if args.sorrys then
        Frontend.collectSorrys step (options := { collectTypeErrors := args.typeErrorsAsGoals })
      else
        pure []
    let messages ← step.msgs.toArray.mapM (·.serialize)
    let newConstants ← if args.newConstants then
        Frontend.collectNewDefinedConstants step
      else
        pure .empty
    return {
      env := step.before,
      boundary,
      invocations,
      sorrys,
      messages,
      newConstants
    }
  let cancelTk? ← match (← get).options.timeout with
    | 0 => pure .none
    | timeout => .some <$> spawnCancelToken (timeout := .ofBitVec timeout)
  let (li, state') ← frontendM.run { cancelTk? } |>.run context |>.run state
  if args.inheritEnv then
    setEnv state'.commandState.env
    if let .some scope := state'.commandState.scopes.head? then
      -- modify the scope
      set { ← getMainState with scope }
  if let .some fileName := args.invocations? then
    let units := li.map λ unit => { invocations? := .some unit.invocations }
    let data : Protocol.FrontendData := { units }
    IO.FS.writeFile fileName (toJson data |>.compress)
  let units ← li.mapM λ step => withEnv step.env do
    let newConstants? := if args.newConstants then
        .some $ step.newConstants.toArray.map λ name => name.toString
      else
        .none
    let (goalStateId?, goals?, goalSrcBoundaries?) ← if step.sorrys.isEmpty then
        pure (.none, .none, .none)
      else do
        let ({ state, srcBoundaries }, goals) ← liftMetaM do
          let result@{state, .. } ← Frontend.sorrysToGoalState step.sorrys
          let goals ← goalSerialize state options
          pure (result, goals)
        let stateId ← newGoalState state
        let srcBoundaries := srcBoundaries.toArray.map (λ (b, e) => (b.byteIdx, e.byteIdx))
        pure (.some stateId, .some goals, .some srcBoundaries)
    let nInvocations? := if args.invocations?.isSome then .some step.invocations.length else .none
    return {
      boundary := step.boundary,
      messages := step.messages,
      nInvocations?,
      goalStateId?,
      goals?,
      goalSrcBoundaries?,
      newConstants?,
    }
  return { units }

end Frontend

/-- Main loop command of the REPL -/
def execute (command: Protocol.Command): MainM Json := do
  let run { α β: Type } [FromJson α] [ToJson β] (comm: α → EMainM β): MainM Json :=
    try
      match fromJson? command.payload with
      | .ok args => do
        let (msg, result) ← IO.FS.withIsolatedStreams (isolateStderr := false) $ comm args
        if !msg.isEmpty then
          IO.eprint s!"stdout: {msg}"
        match result with
        | .ok result =>  return toJson result
        | .error ierror => return toJson ierror
      | .error error => return toJson $ errorCommand s!"Unable to parse json: {error}"
    catch ex : IO.Error =>
      let error : Protocol.InteractionError := { error := "io", desc := ex.toString }
      return toJson error
  match command.cmd with
  | "reset"         => run reset
  | "stat"          => run stat
  | "expr.echo"     => run expr_echo
  | "env.describe"  => run env_describe
  | "env.module_read" => run env_module_read
  | "env.catalog"   => run env_catalog
  | "env.inspect"   => run env_inspect
  | "env.add"       => run env_add
  | "env.save"      => run env_save
  | "env.load"      => run env_load
  | "options.set"   => run options_set
  | "options.print" => run options_print
  | "goal.start"    => run goal_start
  | "goal.tactic"   => run goal_tactic
  | "goal.continue" => run goal_continue
  | "goal.delete"   => run goal_delete
  | "goal.print"    => run goal_print
  | "goal.save"     => run goal_save
  | "goal.load"     => run goal_load
  | "frontend.process" => run frontend_process
  | "frontend.refactor" => run frontend_refactor
  | cmd =>
    let error: Protocol.InteractionError :=
      errorCommand s!"Unknown command {cmd}"
    return toJson error
  where
  errorCommand := errorI "command"
  errorIO := errorI "io"
  -- Command Functions
  reset (_: Protocol.Reset): EMainM Protocol.StatResult := do
    let state ← getMainState
    let nGoals := state.goalStates.size
    set { state with nextId := 0, goalStates := .emptyWithCapacity }
    return { nGoals }
  stat (_: Protocol.Stat): EMainM Protocol.StatResult := do
    let state ← getMainState
    let nGoals := state.goalStates.size
    return { nGoals }
  env_describe (args: Protocol.EnvDescribe): EMainM Protocol.EnvDescribeResult := do
    let result ← runCoreM $ Environment.describe args
    return result
  env_module_read (args: Protocol.EnvModuleRead): EMainM Protocol.EnvModuleReadResult := do
    runCoreM $ Environment.moduleRead args
  env_catalog (args: Protocol.EnvCatalog): EMainM Protocol.EnvCatalogResult := do
    let result ← runCoreM $ Environment.catalog args
    return result
  env_inspect (args: Protocol.EnvInspect): EMainM Protocol.EnvInspectResult := do
    let state ← getMainState
    runCoreM' $ Environment.inspect args state.options
  env_add (args: Protocol.EnvAdd): EMainM Protocol.EnvAddResult := withInheritEnv do
    runCoreM' $ Environment.addDecl args.name (args.levels?.getD #[]) args.type? args.value args.isTheorem
  env_save (args: Protocol.EnvSaveLoad): EMainM Protocol.EnvSaveLoadResult := do
    let env ← MonadEnv.getEnv
    environmentPickle env args.path
    return {}
  env_load (args: Protocol.EnvSaveLoad): EMainM Protocol.EnvSaveLoadResult := do
    let (env, _) ← environmentUnpickle args.path
    setEnv env
    return {}
  expr_echo (args: Protocol.ExprEcho): EMainM Protocol.ExprEchoResult := do
    let state ← getMainState
    let levelNames := (args.levels?.getD #[]).toList.map (·.toName)
    liftExcept $ ← liftTermElabM (levelNames := levelNames) do
      (exprEcho args.expr (expectedType? := args.type?) (options := state.options)).run
  options_set (args: Protocol.OptionsSet): EMainM Protocol.OptionsSetResult := do
    let state ← getMainState
    let options := state.options
    set { state with
      options := {
        -- FIXME: This should be replaced with something more elegant
        printJsonPretty := args.printJsonPretty?.getD options.printJsonPretty,
        printExprPretty := args.printExprPretty?.getD options.printExprPretty,
        printExprAST := args.printExprAST?.getD options.printExprAST,
        printDependentMVars := args.printDependentMVars?.getD options.printDependentMVars,
        noRepeat := args.noRepeat?.getD options.noRepeat,
        printAuxDecls := args.printAuxDecls?.getD options.printAuxDecls,
        printImplementationDetailHyps := args.printImplementationDetailHyps?.getD options.printImplementationDetailHyps
        automaticMode := args.automaticMode?.getD options.automaticMode,
        timeout := args.timeout?.getD options.timeout,
      }
    }
    return {  }
  options_print (_: Protocol.OptionsPrint): EMainM Protocol.Options := do
    return (← getMainState).options
  goal_start (args: Protocol.GoalStart): EMainM Protocol.GoalStartResult := do
    let levelNames := (args.levels?.getD #[]).toList.map (·.toName)
    let expr?: Except _ GoalState ← liftTermElabM (levelNames := levelNames) do
      match args.expr, args.copyFrom with
      | .some expr, .none => goalStartExpr expr |>.run
      | .none, .some copyFrom => do
        (match (← getEnv).find? <| copyFrom.toName with
        | .none => return .error <| Protocol.errorIndex s!"Symbol not found: {copyFrom}"
        | .some cInfo => return .ok (← GoalState.create cInfo.type))
      | _, _ =>
        return .error <| errorI "arguments" "Exactly one of {expr, copyFrom} must be supplied"
    match expr? with
    | .error error => Protocol.throw error
    | .ok goalState =>
      let stateId ← newGoalState goalState
      return { stateId, root := goalState.root.name.toString }
  goal_continue (args: Protocol.GoalContinue): EMainM Protocol.GoalContinueResult := do
    let state ← getMainState
    let .some target := state.goalStates[args.target]? |
      Protocol.throw $ Protocol.errorIndex s!"Invalid state index {args.target}"
    let nextGoalState? : GoalState  ← match args.branch?, args.goals? with
      | .some branchId, .none => do
        match state.goalStates[branchId]? with
        | .none => Protocol.throw $ Protocol.errorIndex s!"Invalid state index {branchId}"
        | .some branch => pure $ target.continue branch
      | .none, .some goals =>
        let goals := goals.toList.map (λ n => { name := n.toName })
        pure $ target.resume goals
      | _, _ => Protocol.throw $ errorI "arguments" "Exactly one of {branch, goals} must be supplied"
    match nextGoalState? with
    | .error error => Protocol.throw $ errorI "structure" error
    | .ok nextGoalState =>
      let nextStateId ← newGoalState nextGoalState
      let goals ← liftMetaM $ goalSerialize nextGoalState (options := state.options)
      return {
        nextStateId,
        goals,
      }
  goal_delete (args: Protocol.GoalDelete): EMainM Protocol.GoalDeleteResult := do
    let state ← getMainState
    let goalStates := args.stateIds.foldl (λ map id => map.erase id) state.goalStates
    set { state with goalStates }
    return {}
  goal_print (args: Protocol.GoalPrint): EMainM Protocol.GoalPrintResult := do
    let state ← getMainState
    let .some goalState := state.goalStates[args.stateId]? |
      Protocol.throw $ Protocol.errorIndex s!"Invalid state index {args.stateId}"
    let result ← liftMetaM <| goalPrint
        goalState
        (rootExpr := args.rootExpr?.getD False)
        (parentExprs := args.parentExprs?.getD False)
        (goals := args.goals?.getD False)
        (extraMVars := args.extraMVars?.getD #[])
        (options := state.options)
    return result
  goal_save (args: Protocol.GoalSave): EMainM Protocol.GoalSaveResult := do
    let state ← getMainState
    let .some goalState := state.goalStates[args.id]? |
      Protocol.throw $ Protocol.errorIndex s!"Invalid state index {args.id}"
    goalStatePickle goalState args.path (background? := .some $ ← getEnv)
    return {}
  goal_load (args: Protocol.GoalLoad): EMainM Protocol.GoalLoadResult := do
    let (goalState, _) ← goalStateUnpickle args.path (background? := .some $ ← getEnv)
    let id ← newGoalState goalState
    return { id }
  frontend_refactor (args : Protocol.FrontendRefactor) : EMainM Protocol.FrontendRefactorResult := do
    try
      let file ← Frontend.runRefactor (← getEnv) args.file
      return { file }
    catch ex : IO.Error =>
      let error : Protocol.InteractionError := { error := "frontend", desc := ex.toString }
      throw error

end Pantograph.Repl
