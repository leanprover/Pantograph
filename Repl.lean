import Pantograph
import Std.Data.HashMap

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

instance : MonadBacktrack State MainM where
  saveState := getMainState
  restoreState := set

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
  let { currNamespace, openDecls, opts := options, .. }:= (← get).scope
  let timeout := (← get).options.timeout
  let cancelTk? ← match timeout with
    | 0 => pure .none
    | _ => .some <$> IO.CancelToken.new
  let coreCtx : Core.Context := {
    (← read).coreContext with
    currNamespace,
    openDecls,
    options,
    initHeartbeats     :=  ← IO.getNumHeartbeats,
    cancelTk?,
  }
  let coreState : Core.State := {
    env := ← getEnv,
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
    runCancelTokenWithTimeout token (timeout := .ofBitVec timeout)
  let (result, state') ← match ← (coreM'.run coreCtx coreState).toIO' with
    | Except.error (Exception.error _ msg)   => Protocol.throw { error := "core", desc := ← msg.toString }
    | Except.error (Exception.internal id _) => Protocol.throw { error := "internal", desc := (← id.getName).toString }
    | Except.ok a                            => pure a
  if (← read).inheritEnv && result matches .ok _ then
    setEnv state'.env
  liftExcept result

def runCoreM' { α } (coreM : Protocol.FallibleT CoreM α) : EMainM α := do
  liftExcept $ ← runCoreM coreM.run

def liftMetaM { α } (metaM : MetaM α) : EMainM α :=
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

section Environment

def env_catalog (_ : Protocol.EnvCatalog) : EMainM Protocol.EnvCatalogResult := runCoreM do
  let env ← MonadEnv.getEnv
  let names := env.constants.fold (init := #[]) λ acc name info =>
    match toFilteredSymbol name info with
    | .some x => acc.push x
    | .none => acc
  return { symbols := names }
def env_inspect (args : Protocol.EnvInspect) : EMainM Protocol.EnvInspectResult := do
  let env ← MonadEnv.getEnv
  let options := (← getMainState).options
  let name :=  args.name
  let info? := env.find? name
  let .some info := info?
    | throw $ Protocol.errorIndex s!"Symbol not found {args.name}"
  runCoreM do
  let module? := env.getModuleIdxFor? name >>=
    (λ idx => env.allImportedModuleNames[idx.toNat]?)
  let value? := match args.value?, info with
    | .some true, _ => info.value?
    | .some false, _ => .none
    | .none, .defnInfo _ => info.value?
    | .none, _ => .none
  let type ← unfoldAuxLemmas info.type
  let value? ← value?.mapM (λ v => unfoldAuxLemmas v)
  -- Information common to all symbols
  let core := {
    type := ← (serializeExpression options type).run',
    isUnsafe := info.isUnsafe,
    value? := ← value?.mapM (λ v => serializeExpression options v |>.run'),
    publicName? := Lean.privateToUserName? name,
    typeDependency? := if args.dependency?.getD false
      then .some <| type.getUsedConstants
      else .none,
    valueDependency? := if args.dependency?.getD false
      then value?.map λ e =>
        e.getUsedConstants.filter (!isNameInternal ·)
      else .none,
    module?,
  }
  let result ← match info with
    | .inductInfo induct => pure { core with inductInfo? := .some {
          induct with
          all := induct.all.toArray,
          ctors := induct.ctors.toArray,
      } }
    | .ctorInfo ctor => pure { core with constructorInfo? := .some {
          ctor with
      } }
    | .recInfo r => pure { core with recursorInfo? := .some {
          r with
          all := r.all.toArray,
          rules := ← r.rules.toArray.mapM (λ rule => do
              pure {
                ctor := rule.ctor,
                nFields := rule.nfields,
                rhs := ← (serializeExpression options rule.rhs).run',
              })
      } }
    | _ => pure core
  let result ← if args.source?.getD false then
      try
        let sourceUri? ← module?.bindM (Server.documentUriFromModule? ·)
        let declRange? ← findDeclarationRanges? name
        let sourceStart? := declRange?.map (·.range.pos)
        let sourceEnd? := declRange?.map (·.range.endPos)
        .pure {
          result with
          sourceUri? := sourceUri?.map (toString ·),
          sourceStart?,
          sourceEnd?,
        }
      catch _e =>
        .pure result
    else
      .pure result
  return result
def env_describe (_ : Protocol.EnvDescribe) : EMainM Protocol.EnvDescribeResult := runCoreM do
  let env ← Lean.MonadEnv.getEnv
  return {
    imports := env.header.imports.map (·.module),
    modules := env.header.moduleNames,
  }
def env_module_read (args : Protocol.EnvModuleRead) : EMainM Protocol.EnvModuleReadResult := runCoreM do
  let env ← Lean.MonadEnv.getEnv
  let .some i := env.header.moduleNames.findIdx? (· == args.module) |
    throwError s!"Module not found {args.module}"
  let data := env.header.moduleData[i]!
  return {
    imports := data.imports.map (·.module),
    constNames := data.constNames,
    extraConstNames := data.extraConstNames,
  }
/-- Elaborates and adds a declaration to the `CoreM` environment. -/
def env_add (args : Protocol.EnvAdd) : EMainM Protocol.EnvAddResult := withInheritEnv <| runCoreM' do
  let { name, levels?, type?, value, isTheorem } := args
  let levels := levels?.getD #[]
  let env ← Lean.MonadEnv.getEnv
  let levelParams := levels.toList
  let tvM: Elab.TermElabM (Except String (Expr × Expr)) :=
    Elab.Term.withLevelNames levelParams do do
    let expectedType?? : Except String (Option Expr) ← ExceptT.run $ type?.mapM λ type => do
      match parseTerm env type with
      | .ok syn => elabTerm syn
      | .error e => MonadExceptOf.throw e
    let expectedType? ← match expectedType?? with
      | .ok t? => pure t?
      | .error e => return .error e
    let value ← match parseTerm env value with
      | .ok syn => do
        try
          let expr ← Elab.Term.elabTerm (stx := syn) (expectedType? := expectedType?)
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          let expr ← instantiateMVars expr
          pure $ expr
        catch ex => return .error (← ex.toMessageData.toString)
      | .error e => return .error e
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let type ← match expectedType? with
      | .some t => pure t
      | .none => Meta.inferType value
    pure $ .ok (← instantiateMVars type, ← instantiateMVars value)
  let (type, value) ← match ← tvM.run' (ctx := {}) |>.run' with
    | .ok t => pure t
    | .error e => Protocol.throw $ Protocol.errorExpr e
  let decl := if isTheorem then
    Lean.Declaration.thmDecl <| Lean.mkTheoremValEx
      (name := name)
      (levelParams := levelParams)
      (type := type)
      (value := value)
      (all := [])
  else
    Lean.Declaration.defnDecl <| Lean.mkDefinitionValEx
      (name := name)
      (levelParams := levelParams)
      (type := type)
      (value := value)
      (hints := Lean.mkReducibilityHintsRegularEx 1)
      (safety := Lean.DefinitionSafety.safe)
      (all := [])
  Lean.addDecl decl
  return {}

end Environment

section Goal

def goal_tactic (args : Protocol.GoalTactic) : EMainM Protocol.GoalTacticResult := do
  let state ← getMainState
  let .some goalState := state.goalStates[args.stateId]?
    | throw $ Protocol.errorIndex s!"Invalid state index {args.stateId}"
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
    match args.tactic?, args.mode?, args.expr?, args.have?, args.let?, args.draft? with
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
      let binderName := args.binderName?.getD .anonymous
      pure $ Except.ok $ ← goalState.tryHave site binderName type
    | .none, .none, .none, .none, .some type, .none => do
      let binderName := args.binderName?.getD .anonymous
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

def frontend_distil (args : Protocol.FrontendDistil) : EMainM Protocol.FrontendDistilResult := do
  let config := {
    binderName? := args.binderName?,
    ignoreValues := args.ignoreValues,
  }
  let targets ← Frontend.distilSearchTargets (← getEnv) args.file config
  let targets ← targets.mapM λ _dst@{ goalState } => do
    let stateId ← newGoalState goalState
    let goals ← runCoreM $ goalState.serializeGoals (options := (← get).options) |>.run'
    return { stateId, goals }
  return { targets }

structure CompilationUnit where
  -- Environment immediately before the unit
  env : Environment
  boundary : Nat × Nat
  invocations : List Protocol.InvokedTactic
  messages : Array SerialMessage
  newConstants : NameSet

export Frontend (defaultFileName)

def frontend_process (args : Protocol.FrontendProcess) : EMainM Protocol.FrontendProcessResult := do
  let (fileName, file) ← match args.fileName?, args.file? with
    | .some fileName, .none => do
      let file ← IO.FS.readFile fileName
      pure (fileName, file)
    | .none, .some file =>
      pure (defaultFileName, file)
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
    let messages ← step.msgs.toArray.mapM (·.serialize)
    let newConstants ← if args.newConstants then
        step.newConstants
      else
        pure .empty
    return {
      env := step.before,
      boundary,
      invocations,
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
      -- modify the scope to take into account `open` statements
      set { ← getMainState with scope }
  if let .some fileName := args.invocations? then
    let units := li.map λ unit => { invocations? := .some unit.invocations }
    let data : Protocol.FrontendData := { units }
    IO.FS.writeFile fileName (toJson data |>.compress)
  let units ← li.mapM λ step => withEnv step.env do
    let newConstants? := if args.newConstants then
        .some $ step.newConstants.toArray
      else
        .none
    let nInvocations? := if args.invocations?.isSome then .some step.invocations.length else .none
    return {
      boundary := step.boundary,
      messages := step.messages,
      nInvocations?,
      newConstants?,
    }
  return { units }

end Frontend

/-- Main loop command of the REPL -/
def execute (command : Protocol.Command) : MainM Json := do
  let run { α β } [FromJson α] [ToJson β] (comm : α → EMainM β) : MainM Json := do
    let args ← match fromJson? command.payload with
      | .ok args => pure args
      | .error error => return toJson $ errorCommand s!"Unable to parse json: {error}"
    try
      let (out, result) ← IO.FS.withIsolatedStreams (isolateStderr := false) do
        commitIfNoEx $ comm args
      if !out.isEmpty then
        IO.eprint s!"stdout: {out}"
      match result with
      | .ok result =>  return toJson result
      | .error ierror => return toJson ierror
    catch ex : IO.Error =>
      let error : Protocol.InteractionError := { error := "io", desc := ex.toString }
      return toJson error
  match command.cmd with
  | "reset"         => run reset
  | "stat"          => run stat
  | "options.set"   => run options_set
  | "options.print" => run options_print
  | "expr.echo"     => run expr_echo
  | "env.describe"  => run env_describe
  | "env.module_read" => run env_module_read
  | "env.catalog"   => run env_catalog
  | "env.inspect"   => run env_inspect
  | "env.add"       => run env_add
  | "env.save"      => run env_save
  | "env.load"      => run env_load
  | "env.parse"     => run env_parse
  | "goal.start"    => run goal_start
  | "goal.tactic"   => run goal_tactic
  | "goal.continue" => run goal_continue
  | "goal.delete"   => run goal_delete
  | "goal.print"    => run goal_print
  | "goal.save"     => run goal_save
  | "goal.load"     => run goal_load
  | "frontend.process" => run frontend_process
  | "frontend.distil"  => run frontend_distil
  | "frontend.track"   => run frontend_track
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
    let levelNames := (args.levels?.getD #[]).toList
    liftExcept $ ← liftTermElabM (levelNames := levelNames) do
      (exprEcho args.expr (expectedType? := args.type?) (options := state.options)).run
  env_parse (args : Protocol.EnvParse) : EMainM Protocol.EnvParseResult := do
    let category := args.category
    match runParserCategory' (← getEnv) category args.input with
    | .ok (_, p) => return { pos := p.byteIdx }
    | .error desc => throw { error := "parse", desc }
  goal_start (args: Protocol.GoalStart): EMainM Protocol.GoalStartResult := do
    let levelNames := (args.levels?.getD #[]).toList
    let expr?: Except _ GoalState ← liftTermElabM (levelNames := levelNames) do
      match args.expr, args.copyFrom with
      | .some expr, .none => goalStartExpr expr |>.run
      | .none, .some copyFrom => do
        (match (← getEnv).find? copyFrom with
        | .none => return .error <| Protocol.errorIndex s!"Symbol not found: {copyFrom}"
        | .some cInfo => return .ok (← GoalState.create cInfo.type))
      | _, _ =>
        return .error <| errorI "arguments" "Exactly one of {expr, copyFrom} must be supplied"
    match expr? with
    | .error error => Protocol.throw error
    | .ok goalState =>
      let stateId ← newGoalState goalState
      return { stateId, root := goalState.root.name }
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
        let goals := goals.toList.map (⟨·⟩)
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
  frontend_track (args : Protocol.FrontendTrack) : EMainM Protocol.FrontendTrackResult := do
    let env ← getEnv
    let collectOne (source : String) : IO _ := do
      let (context, state) ← do Frontend.createContextStateFromFile source (env? := env)
      let m := Frontend.collectEndState
      m.run { } |>.run context |>.run' state
    let srcState ← collectOne args.src
    let dstState ← collectOne args.dst
    let srcMessages ← srcState.messages.toArray.mapM (·.serialize)
    let dstMessages ← dstState.messages.toArray.mapM (·.serialize)
    if srcMessages.any (·.severity ==.error) ∨ dstMessages.any (·.severity ==.error) then
      return { srcMessages, dstMessages }
    let result? ← show IO _ from ExceptT.run do
      checkEnvConflicts env srcState.env dstState.env
    match result? with
    | .error e => return { failure? := .some e }
    | .ok _ => return {}
  frontend_refactor (args : Protocol.FrontendRefactor) : EMainM Protocol.FrontendRefactorResult := do
    try
      let coreOptions? ← show IO _ from ExceptT.run $ args.coreOptions.foldlM (init := {}) λ acc opt =>
        setOptionFromString' acc opt
      match coreOptions? with
      | .ok coreOptions => do
        let file ← Frontend.runRefactor (← getEnv) args.file { coreOptions }
        return { file }
      | .error e =>
        throw $ errorI "parse" e
    catch ex : IO.Error =>
      let error : Protocol.InteractionError := { error := "frontend", desc := ex.toString }
      throw error
