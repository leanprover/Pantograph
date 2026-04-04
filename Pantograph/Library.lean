import Pantograph.Environment
import Pantograph.Goal
import Pantograph.Protocol
import Pantograph.Delab

namespace Pantograph

open Lean

/-- This is better than the default version since it handles `.` and doesn't
 crash the program when it fails. -/
def setOptionFromString' (opts : Options) (entry : String) : ExceptT String IO Options := do
  let ps := (entry.splitOn "=").map String.trimAscii
  let [key, val] ← pure ps | throw "invalid configuration option entry, it must be of the form '<key> = <value>'"
  let key := key.toName
  let defValue ← getOptionDefaultValue key
  match defValue with
  | DataValue.ofString _ => pure $ opts.set key val.toString
  | DataValue.ofBool _   =>
    match val with
    | "true" => pure $ opts.setBool key true
    | "false" => pure $ opts.setBool key false
    | _ => throw  s!"invalid Bool option value '{val}'"
  | DataValue.ofName _   => pure $ opts.set key val.toName
  | DataValue.ofNat _    =>
    match val.toNat? with
    | none   => throw s!"invalid Nat option value '{val}'"
    | some v => pure $ opts.set key v
  | DataValue.ofInt _    =>
    match val.toInt? with
    | none   => throw s!"invalid Int option value '{val}'"
    | some v => pure $ opts.set key v
  | DataValue.ofSyntax _ => throw s!"invalid Syntax option value"

def runMetaM { α } (metaM: MetaM α): CoreM α :=
  metaM.run'

def errorI (type desc: String): Protocol.InteractionError := { error := type, desc := desc }

/-- Adds the given paths to Lean package search path. This must run with at
least an empty string, otherwise Lean will not be able to find any symbols -/
@[export pantograph_init_search]
unsafe def initSearch (sp: String := ""): IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot) (sp := System.SearchPath.parse sp)

/-- Creates a Core.Context object needed to run all monads -/
@[export pantograph_create_core_context]
def createCoreContext (options : Array String) : IO Core.Context := do
  let options? ← options.foldlM setOptionFromString' Options.empty |>.run
  let options ← match options? with
    | .ok options => pure options
    | .error e => throw $ IO.userError s!"Options cannot be parsed: {e}"
  return {
    currNamespace := `Cirno,
    openDecls := [],     -- No 'open' directives needed
    fileName := "<Pantograph>",
    fileMap := { source := "", positions := #[0] },
    options,
    maxRecDepth := maxRecDepth.get options,
  }

/-- Creates a Core.State object needed to run all monads -/
@[export pantograph_create_core_state]
def createCoreState (env : Environment) : IO Core.State := do
  return { env }

@[export pantograph_parse_elab_type_m]
def parseElabType (type : String) : Protocol.FallibleT Elab.TermElabM Expr := do
  let env ← MonadEnv.getEnv
  let syn ← match parseTerm env type with
    | .error str => Protocol.throw $ errorI "parse" str
    | .ok syn => pure syn
  match ← elabType syn with
  | .error str => Protocol.throw $ errorI "elab" str
  | .ok expr => return (← instantiateMVars expr)

/-- This must be a TermElabM since the parsed expr contains extra information -/
@[export pantograph_parse_elab_expr_m]
def parseElabExpr (expr : String) (expectedType? : Option String := .none) : Protocol.FallibleT Elab.TermElabM Expr := do
  let env ← MonadEnv.getEnv
  let expectedType? ← expectedType?.mapM parseElabType
  let syn ← match parseTerm env expr with
    | .error str => Protocol.throw $ errorI "parse" str
    | .ok syn => pure syn
  match ← elabTerm syn expectedType? with
  | .error str => Protocol.throw $ errorI "elab" str
  | .ok expr => return (← instantiateMVars expr)

@[export pantograph_expr_echo_m]
def exprEcho (expr: String) (expectedType?: Option String := .none) (options: @&Protocol.Options := {}):
    Protocol.FallibleT Elab.TermElabM Protocol.ExprEchoResult := do
  let expr ← parseElabExpr expr expectedType?
  try
    let type ← unfoldAuxLemmas (← Meta.inferType expr)
    return {
        type := (← serializeExpression options type),
        expr := (← serializeExpression options expr),
    }
  catch exception =>
    Protocol.throw $ errorI "typing" (← exception.toMessageData.toString)

@[export pantograph_goal_start_expr_m]
def goalStartExpr (expr: String) : Protocol.FallibleT Elab.TermElabM GoalState := do
  let t ← parseElabType expr
  Elab.Term.synthesizeSyntheticMVarsUsingDefault
  GoalState.create t

@[export pantograph_goal_serialize_m]
def goalSerialize (state: GoalState) (options: @&Protocol.Options): CoreM (Array Protocol.Goal) :=
  runMetaM <| state.serializeGoals options

@[export pantograph_goal_print_m]
def goalPrint (state: GoalState) (rootExpr: Bool) (parentExprs: Bool)
  (goals: Bool) (extraMVars : Array Name) (options: @&Protocol.Options)
  : CoreM Protocol.GoalPrintResult := runMetaM do
  state.restoreMetaM

  let rootExpr? := state.rootExpr?
  let root? ← if rootExpr then
      rootExpr?.mapM λ expr => state.withRootContext do
        serializeExpression options (← instantiateAll expr)
    else
      pure .none
  let parentExprs? ← if parentExprs then
      .some <$> state.parentMVars.mapM λ parent => parent.withContext do
        let val? := state.getMVarEAssignment parent
        val?.mapM λ val => do
          serializeExpression options (← instantiateAll val)
    else
      pure .none
  let goals ← if goals then
      goalSerialize state options
    else
      pure #[]
  let extraMVars ← extraMVars.mapM λ name => do
    let mvarId: MVarId := ⟨name⟩
    let .some _ ← mvarId.findDecl? | return {}
    state.withContext mvarId do
      let .some expr ← getExprMVarAssignment? mvarId | return {}
      serializeExpression options (← instantiateAll expr)
  let env ← getEnv
  return {
    root?,
    parentExprs?,
    goals,
    extraMVars,
    rootHasSorry := rootExpr?.map (·.hasSorry) |>.getD false,
    rootHasUnsafe := rootExpr?.map (env.hasUnsafe ·) |>.getD false,
    rootHasMVar := rootExpr?.map (·.hasExprMVar) |>.getD false,
  }

@[export pantograph_goal_have_m]
protected def GoalState.tryHave (state: GoalState) (site : Site) (binderName: Name) (type: String): Elab.TermElabM TacticResult := do
  let type ← match (← parseTermM type) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  state.restoreElabM
  state.tryTacticM site $ Tactic.evalHave binderName type
protected def GoalState.tryLet (state : GoalState) (site : Site) (binderName : Name) (type : String)
    : Elab.TermElabM TacticResult := do
  state.restoreElabM
  let type ← match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `term)
    (input := type)
    (fileName := ← getFileName) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  state.tryTacticM site $ Tactic.evalLet binderName type
@[export pantograph_goal_try_define_m]
protected def GoalState.tryDefine (state: GoalState) (site : Site) (binderName: Name) (expr: String): Elab.TermElabM TacticResult := do
  let expr ← match (← parseTermM expr) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  state.restoreElabM
  state.tryTacticM site $ Tactic.evalDefine binderName expr
@[export pantograph_goal_try_draft_m]
protected def GoalState.tryDraft (state: GoalState) (site : Site) (expr: String): Elab.TermElabM TacticResult := do
  let expr ← match (← parseTermM expr) with
    | .ok syn => pure syn
    | .error error => return .parseError error
  state.restoreElabM
  state.tryTacticM site $ Tactic.evalDraft expr

-- Cancel the token after a timeout.
@[export pantograph_run_cancel_token_with_timeout_m]
def runCancelTokenWithTimeout (cancelToken : IO.CancelToken) (timeout : UInt32) : IO Unit := do
  let _ ← IO.asTask do
    IO.sleep timeout
    cancelToken.set
  return ()

def spawnCancelToken (timeout : UInt32) : IO IO.CancelToken := do
  let token ← IO.CancelToken.new
  runCancelTokenWithTimeout token timeout
  return token
