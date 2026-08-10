import Pantograph.Library
import Pantograph.Serial

import LSpec
import PantographTest.Common

open Lean

namespace Pantograph.Test.Serial

structure MultiState where
  coreContext : Core.Context
  env: Environment

abbrev TestM := TestT $ StateRefT MultiState $ IO

instance : MonadEnv TestM where
  getEnv      := return (← getThe MultiState).env
  modifyEnv f := do modifyThe MultiState fun s => { s with env := f s.env }

def runCoreM { α } (state : Core.State) (testCoreM : TestT CoreM α) : TestM (α × Core.State) := do
  let multiState ← getThe MultiState
  let coreM := runTestWithResult testCoreM
  match ← (coreM.run multiState.coreContext state).toBaseIO with
  | .error e => do
    throw $ .userError $ ← e.toMessageData.toString
  | .ok ((a, tests), state') => do
    set $ (← getThe LSpec.TestSeq) ++ tests
    return (a, state')

def test_pickling_environment : TestM Unit := do
  let env0 ← getEnv
  let coreSrc : Core.State := { env := env0 }
  let coreDst : Core.State := { env := env0 }

  let name := `mystery
  IO.FS.withTempFile λ _ envPicklePath => do
  IO.FS.removeFile envPicklePath
  unsafe do
    Lean.enableInitializersExecution
  let ((), _) ← runCoreM coreSrc do
    let type: Expr := .forallE `p (.sort 0) (.forallE `h (.bvar 0) (.bvar 1) .default) .default
    let value: Expr := .lam `p (.sort 0) (.lam `h (.bvar 0) (.bvar 0) .default) .default
    let c := Declaration.thmDecl <| mkTheoremValEx
      (name := name)
      (levelParams := [])
      (type := type)
      (value := value)
      (all := [])
    addDecl c
    if (← Core.getMessageLog).hasErrors then
      let log ← Core.getMessageLog
      IO.eprintln "has errors!"
      log.forM λ msg => do
        IO.eprintln s!"{← msg.toString}"
    unless (← getEnv).find? name |>.isSome do
      throwError s!"Could not add definition {name}"
    environmentPickle (← getEnv) envPicklePath

  let _ ← runCoreM coreDst do
    checkTrue "Path exists" (← envPicklePath.pathExists)
    let (env', region) ← environmentUnpickle envPicklePath
    if (← Core.getMessageLog).hasErrors then
      let log ← Core.getMessageLog
      IO.eprintln "has errors!"
      log.forM λ msg => do
        IO.eprintln s!"{← msg.toString}"
    checkTrue s!"Has symbol {name}" (env'.find? name).isSome
    let anotherName := `mystery2
    checkTrue s!"Doesn't have symbol {anotherName}" (env'.find? anotherName).isNone
    unsafe do region.free

def test_goal_state_simple : TestM Unit := do
  let coreSrc : Core.State := { env := ← getEnv }
  let coreDst : Core.State := { env := ← getEnv }
  IO.FS.withTempFile λ _ statePath => do
  let type: Expr := .forallE `p (.sort 0) (.forallE `h (.bvar 0) (.bvar 1) .default) .default
  let stateGenerate : MetaM GoalState := runTermElabMInMeta do
    GoalState.create type

  let ((), _) ← runCoreM coreSrc do
    let state ← stateGenerate.run'
    goalStatePickle state statePath

  let ((), _) ← runCoreM coreDst do
    let (goalState, region) ← goalStateUnpickle statePath (← getEnv)
    let metaM : MetaM (List Expr) := do
      goalState.goals.mapM λ goal => goalState.withContext goal goal.getType
    let types ← metaM.run'
    checkTrue "Goals" $ types[0]!.equal type
    unsafe do region.free

def test_pickling_env_extensions : TestM Unit := do
  let coreSrc : Core.State := { env := ← getEnv }
  let coreDst : Core.State := { env := ← getEnv }
  IO.FS.withTempFile λ _ statePath => do
  let ((), _) ← runCoreM coreSrc $ transformTestT runTermElabMInCore do
    let .ok e ← elabTerm (← `(term|(2: Nat) ≤ 3 ∧ (3: Nat) ≤ 5)) .none | unreachable!
    let state ← GoalState.create e
    let .success state _ ← state.tacticOn' 0 (← `(tactic|apply And.intro)) | unreachable!

    let goal := state.goals[0]!
    let type ← goal.withContext do
      let .ok type ← elabTerm (← `(term|(2: Nat) ≤ 3)) (.some $ .sort 0) | unreachable!
      instantiateMVars type
    let .success state1 _ ← state.tryTacticM goal (Tactic.assignWithAuxLemma type) | unreachable!
    let parentExpr := state1.parentExpr!
    checkTrue "src has aux lemma" $ parentExpr.getUsedConstants.any isAuxLemma
    goalStatePickle state1 statePath
  let ((), _) ← runCoreM coreDst $ transformTestT runTermElabMInCore do
    let (state1, region) ← goalStateUnpickle statePath (← getEnv)
    let parentExpr := state1.parentExpr!
    checkTrue "dst has aux lemma" $ parentExpr.getUsedConstants.any isAuxLemma
    unsafe do region.free

  return ()

/-- Synthetic mvars in this case creates closures. These cannot be pickled. -/
def test_pickling_synthetic_mvars : TestM Unit := do
  let coreSrc : Core.State := { env := ← getEnv }
  IO.FS.withTempFile λ _ statePath => do
  let stateGenerate : MetaM GoalState := runTermElabMInMeta do
    let type ← Elab.Term.elabTerm (← `(term|(0 : Nat) < 1)) .none
    let state ← GoalState.create type
    let .success state _ ← state.tryHave .unfocus `h "0 < 2" | unreachable!
    assert! state.savedState.term.elab.syntheticMVars.size > 0
    return state

  let ((), _) ← runCoreM coreSrc do
    let state ← stateGenerate.run'
    goalStatePickle state statePath

structure Test where
  name : String
  routine: TestM Unit

protected def Test.run (test: Test) (env: Environment) : IO LSpec.TestSeq := do
  -- Create the state
  let state : MultiState := {
    coreContext := ← createCoreContext #[],
    env,
  }
  match ← ((runTest $ test.routine).run' state).toBaseIO with
  | .ok e => return e
  | .error e =>
    return LSpec.check s!"Emitted exception: {e.toString}" (e.toString == "")

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests: List Test := [
    { name := "environment", routine := test_pickling_environment, },
    { name := "goal simple", routine := test_goal_state_simple, },
    { name := "goal synthetic mvars", routine := test_pickling_synthetic_mvars, },
    { name := "extensions", routine := test_pickling_env_extensions, },
  ]
  tests.map (fun test => (test.name, test.run env))

end Pantograph.Test.Serial
