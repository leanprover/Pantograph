import Pantograph.Goal
import Pantograph.Library
import Pantograph.Protocol
import Pantograph.Frontend
import LSpec

namespace Pantograph

open Lean

deriving instance Repr for Expr
-- Use strict equality check for expressions
instance : BEq Expr := ⟨Expr.equal⟩

def uniq (n: Nat): Name := .num (.str .anonymous "_uniq") n

-- Auxiliary functions
namespace Protocol
def Goal.devolatilizeVars (goal: Goal): Goal :=
  {
    goal with
    vars := goal.vars.map removeInternalAux,

  }
  where removeInternalAux (v: Variable): Variable :=
    {
      v with
      name := .anonymous
    }
/-- Set internal names to "" -/
def Goal.devolatilize (goal: Goal): Goal :=
  {
    goal.devolatilizeVars with
    name := .anonymous,
  }

deriving instance DecidableEq, Repr for Name
deriving instance DecidableEq, Repr for Expression
deriving instance DecidableEq, Repr for Variable
deriving instance DecidableEq, Repr for Goal
deriving instance DecidableEq, Repr for ExprEchoResult
deriving instance DecidableEq, Repr for InteractionError
deriving instance DecidableEq, Repr for Option
end Protocol

namespace Condensed

deriving instance BEq, Repr for LocalDecl
deriving instance BEq, Repr for Goal

-- Enable string interpolation
instance : ToString FVarId where
  toString id := id.name.toString
instance : ToString MVarId where
  toString id := id.name.toString

protected def LocalDecl.devolatilize (decl: LocalDecl): LocalDecl :=
  {
    decl with fvarId := { name := .anonymous }
  }
protected def Goal.devolatilize (goal: Goal): Goal :=
  {
    goal with
    mvarId := { name := .anonymous },
    context := goal.context.map LocalDecl.devolatilize
  }

end Condensed

def GoalState.get! (state: GoalState) (i: Nat): MVarId := state.goals[i]!
def GoalState.tacticOn (state: GoalState) (goalId: Nat) (tactic: String) := state.tryTactic (state.get! goalId) tactic
def GoalState.tacticOn' (state: GoalState) (goalId: Nat) (tactic: TSyntax `tactic) :=
  state.tryTacticM (state.get! goalId) (Elab.Tactic.evalTactic tactic) true

def TacticResult.toString : TacticResult → String
  | .success state _messages => s!".success ({state.goals.length} goals)"
  | .failure messages =>
    s!".failure ({messages.size} messages)"
  | .parseError error => s!".parseError {error}"
  | .invalidAction error => s!".invalidAction {error}"

namespace Test

def expectationFailure (desc: String) (error: String): LSpec.TestSeq := LSpec.test desc (LSpec.ExpectationFailure "ok _" error)
def assertUnreachable (message: String): LSpec.TestSeq := LSpec.check message false

def parseFailure (error: String) := expectationFailure "parse" error
def elabFailure (error: String) := expectationFailure "elab" error

def runCoreMSeq (env: Environment) (coreM: CoreM LSpec.TestSeq) (options: Array String := #[]): IO LSpec.TestSeq := do
  let coreContext: Core.Context ← createCoreContext options
  match ← (coreM.run' coreContext { env := env }).toBaseIO with
  | .error exception =>
    return LSpec.test "Exception" (s!"internal exception #{← exception.toMessageData.toString}" = "")
  | .ok a            => return a
def runMetaMSeq (env: Environment) (metaM: MetaM LSpec.TestSeq): IO LSpec.TestSeq :=
  runCoreMSeq env metaM.run'
def runTermElabMInMeta { α } (termElabM: Elab.TermElabM α): MetaM α :=
  termElabM.run' (ctx := defaultElabContext)
def runTermElabMInCore { α } (termElabM: Elab.TermElabM α): CoreM α :=
  (runTermElabMInMeta termElabM).run'
def runTermElabMSeq (env: Environment) (termElabM: Elab.TermElabM LSpec.TestSeq): IO LSpec.TestSeq :=
  runMetaMSeq env $ termElabM.run' (ctx := defaultElabContext)

def exprToStr (e: Expr): MetaM String := toString <$> Meta.ppExpr e

def strToTermSyntax (s: String): CoreM Syntax := do
  let .ok stx := Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `term)
    (input := s)
    (fileName := ← getFileName) | panic! s!"Failed to parse {s}"
  return stx
def parseSentence (s : String) (expectedType? : Option Expr := .none) : Elab.TermElabM Expr := do
  let stx ← match Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `term)
    (input := s)
    (fileName := ← getFileName) with
    | .ok syn => pure syn
    | .error error => throwError "Failed to parse: {error}"
  Elab.Term.elabTerm (stx := stx) expectedType?

def runTacticOnMVar (tacticM: Elab.Tactic.TacticM Unit) (goal: MVarId): Elab.TermElabM (List MVarId) := do
    let (_, newGoals) ← tacticM { elaborator := .anonymous } |>.run { goals := [goal] }
    return newGoals.goals
def mvarUserNameAndType (mvarId: MVarId): MetaM (Name × String) := do
  let name := (← mvarId.getDecl).userName
  let t ← exprToStr (← mvarId.getType)
  return (name, t)

def extractEnvAfterUnit (env : Environment) (unit : String)
  : IO Environment := do
  let (context, state) ← Frontend.createContextStateFromFile
    (file := unit) (env? := .some env)
  let m := show Frontend.FrontendM _ from Frontend.executeFrontend λ _ => pure ()
  let (_, state) ← m.run {} |>.run context |>.run state
  return state.commandState.env

-- Monadic testing

abbrev TestT := StateRefT' IO.RealWorld LSpec.TestSeq

section Monadic

variable [Monad m] [MonadLiftT (ST IO.RealWorld) m]

def addTest (test: LSpec.TestSeq) : TestT m Unit := do
  set $ (← get) ++ test

def checkEq [DecidableEq α] [Repr α] (desc : String) (lhs rhs : α) : TestT m Unit := do
  addTest $ LSpec.check desc (lhs = rhs)
def checkTrue (desc : String) (flag : Bool) : TestT m Unit := do
  addTest $ LSpec.check desc flag
def checkFalse (desc : String) (flag : Bool) : TestT m Unit := do
  addTest $ LSpec.check desc !flag
def fail (desc : String) : TestT m Unit := do
  addTest $ LSpec.check desc false

def runTest (t: TestT m Unit): m LSpec.TestSeq :=
  Prod.snd <$> t.run LSpec.TestSeq.done
def runTestWithResult { α } (t: TestT m α): m (α × LSpec.TestSeq) :=
  t.run LSpec.TestSeq.done
def runTestCoreM (env: Environment) (coreM: TestT CoreM Unit) (options: Array String := #[]): IO LSpec.TestSeq := do
  runCoreMSeq env (runTest coreM) options

end Monadic

def runTestTermElabM (env: Environment) (t: TestT Elab.TermElabM Unit):
  IO LSpec.TestSeq :=
  runTermElabMSeq env $ runTest t
def transformTestT { α } { μ μ' : Type → Type }
    [Monad μ] [Monad μ'] [MonadLiftT (ST IO.RealWorld) μ] [MonadLiftT (ST IO.RealWorld) μ']
    (tr : {β : Type} → μ β  → μ' β) (m : TestT μ α) : TestT μ' α := do
  let tests ← get
  let (a, tests) ← tr (β := α × LSpec.TestSeq) (m.run tests)
  set tests
  return a

def cdeclOf (userName : Name) (type : Expr) : Condensed.LocalDecl :=
  { userName, type }

def buildGoal (nameType : List (Name × String)) (target : String) (userName?: Option Name := .none):
    Protocol.Goal :=
  {
    userName?,
    target := { pp? := .some target},
    vars := (nameType.map fun x => ({
      userName := x.fst,
      type? := .some { pp? := .some x.snd },
    })).toArray
  }

namespace Tactic

/-- Create an aux lemma and assigns it to `mvarId`, which is circuitous, but
exercises the aux lemma generator. -/
def assignWithAuxLemma (type : Expr) (value? : Option Expr := .none) : Elab.Tactic.TacticM Unit := do
  let type ← instantiateMVars type
  let value ← match value? with
    | .some value => instantiateMVars value
    | .none => Meta.mkSorry type (synthetic := false)
  if type.hasExprMVar then
    throwError "Type has expression mvar"
  if value.hasExprMVar then
    throwError "value has expression mvar"
  let goal ← Elab.Tactic.getMainGoal
  goal.withContext do
  let name ← Meta.mkAuxLemma [] type value
  unless ← Meta.isDefEq type (← goal.getType) do
    throwError "Type provided is incorrect"
  goal.assign (.const name [])
  Elab.Tactic.pruneSolvedGoals

/-- A function that takes many iterations to finish -/
partial def collatz (n : Nat) : Elab.Tactic.TacticM Unit := do
  if n ≤ 1 then
    let g ← Elab.Tactic.getMainGoal
    g.assign (.lit (.natVal n))
    Elab.Tactic.pruneSolvedGoals
  else if n % 2 == 0 then
    Meta.withIncRecDepth do
      collatz (n / 2)
  else
    Meta.withIncRecDepth do
      collatz (3 * n + 1)

end Tactic

end Test

end Pantograph
