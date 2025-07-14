import Pantograph
import Repl
import Test.Common

import LSpec

open Lean Pantograph
namespace Pantograph.Test.Frontend

open Frontend

def runFrontend { α } (source: String) (f : CompilationStep → FrontendM α) (timeout : UInt32 := 0): MetaM (List α) := do
  let filename := "<anonymous>"
  let (context, state) ← do createContextStateFromFile source filename (← getEnv) {}
  let m := mapCompilationSteps f
  let cancelTk? ← match timeout with
    | 0 => pure .none
    | timeout => .some <$> spawnCancelToken timeout
  m.run { cancelTk? } |>.run context |>.run' state

def test_open : TestT MetaM Unit := do
  let sketch := "
open Nat
example : ∀ (n : Nat), n + 1 = Nat.succ n := by
  intro
  apply add_one
  "
  let errors ← runFrontend sketch λ step => step.msgs.mapM (·.toString)
  checkEq "errors" errors [[], []]

def collectSorrysFromSource (source: String) (options : Frontend.GoalCollectionOptions := {})
    : MetaM (List GoalState) := do
  let filename := "<anonymous>"
  let (context, state) ← do Frontend.createContextStateFromFile source filename (← getEnv) {}
  let m := Frontend.mapCompilationSteps λ step => do
    return (step.before, ← Frontend.collectSorrys step options)
  let li ← m.run {} |>.run context |>.run' state
  let goalStates ← li.filterMapM λ (env, sorrys) => withEnv env do
    if sorrys.isEmpty then
      return .none
    let { state, .. } ← Frontend.sorrysToGoalState sorrys
    return .some state
  return goalStates

def test_multiple_sorrys_in_proof : TestT MetaM Unit := do
  let sketch := "
theorem plus_n_Sm_proved_formal_sketch : ∀ n m : Nat, n + (m + 1) = (n + m) + 1 := by
   have h_nat_add_succ: ∀ n m : Nat, n = m := sorry
   sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! "Incorrect number of states"
  addTest $ LSpec.check "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize) = #[
    {
      target := { pp? := "∀ (n m : Nat), n = m" },
      vars := #[
      ]
    },
    {
      target := { pp? := "∀ (n m : Nat), n + (m + 1) = n + m + 1" },
      vars := #[{
        userName := "h_nat_add_succ",
        type? := .some { pp? := "∀ (n m : Nat), n = m" },
      }],
    }
  ])

def test_sorry_in_middle: TestT MetaM Unit := do
  let sketch := "
example : ∀ (n m: Nat), n + m = m + n := by
  intros n m
  sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! s!"Incorrect number of states: {goalStates.length}"
  addTest $ LSpec.check "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize) = #[
    {
      target := { pp? := "n + m = m + n" },
      vars := #[{
           userName := "n",
           type? := .some { pp? := "Nat" },
        }, {
           userName := "m",
           type? := .some { pp? := "Nat" },
        }
      ],
    }
  ])

def test_sorry_in_induction : TestT MetaM Unit := do
  let sketch := "
example : ∀ (n m: Nat), n + m = m + n := by
  intros n m
  induction n with
  | zero =>
    have h1 : 0 + m = m := sorry
    sorry
  | succ n ih =>
    have h2 : n + m = m := sorry
    sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! s!"Incorrect number of states: {goalStates.length}"
  addTest $ LSpec.check "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize) = #[
    {
      target := { pp? := "0 + m = m" },
      vars := #[{
        userName := "m",
        type? := .some { pp? := "Nat" },
      }]
    },
    {
      userName? := .some "zero",
      target := { pp? := "0 + m = m + 0" },
      vars := #[{
        userName := "m",
        type? := .some { pp? := "Nat" },
      }, {
        userName := "h1",
        type? := .some { pp? := "0 + m = m" },
      }]
    },
    {
      target := { pp? := "n + m = m" },
      vars := #[{
        userName := "m",
        type? := .some { pp? := "Nat" },
      }, {
        userName := "n",
        type? := .some { pp? := "Nat" },
      }, {
        userName := "ih",
        type? := .some { pp? := "n + m = m + n" },
      }]
    },
    {
      userName? := .some "succ",
      target := { pp? := "n + 1 + m = m + (n + 1)" },
      vars := #[{
        userName := "m",
        type? := .some { pp? := "Nat" },
      }, {
        userName := "n",
        type? := .some { pp? := "Nat" },
      }, {
        userName := "ih",
        type? := .some { pp? := "n + m = m + n" },
      },  {
        userName := "h2",
        type? := .some { pp? := "n + m = m" },
      }]
    }
  ])

def test_sorry_in_coupled: TestT MetaM Unit := do
  let sketch := "
example : ∀ (y: Nat), ∃ (x: Nat), y + 1 = x := by
  intro y
  apply Exists.intro
  case h => sorry
  case w => sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! s!"Incorrect number of states: {goalStates.length}"
  addTest $ LSpec.check "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize) = #[
    {
      target := { pp? := "y + 1 = ?w" },
      vars := #[{
           userName := "y",
           type? := .some { pp? := "Nat" },
        }
      ],
    },
    {
      userName? := .some "w",
      target := { pp? := "Nat" },
      vars := #[{
           userName := "y",
           type? := .some { pp? := "Nat" },
        }
      ],
    }
  ])

def test_sorry_with_local_instance : TestT MetaM Unit := do
  let sketch := "
def test (α : Type) [s : Inhabited α] : α := @Inhabited.default α s
example (α : Type) [Inhabited α] : α := sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! s!"Incorrect number of states: {goalStates.length}"
  let result ← runTermElabMInMeta $ goalState.tryTactic .unfocus "exact test α"
  checkTrue "success" $ result matches .success ..
  match result with
  | .success .. => return ()
  | .failure messages =>
    let messages ← messages.mapM (·.toString)
    fail s!"Could not execute tactic {messages}"
  | .parseError e =>
    fail s!"Parse error: {e}"
  | .invalidAction e =>
    fail s!"Invalid action: {e}"

def test_environment_capture: TestT MetaM Unit := do
  let sketch := "
def mystery (n: Nat) := n + 1

example (n: Nat) : mystery n + 1 = n + 2 := sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! s!"Incorrect number of states: {goalStates.length}"
  addTest $ LSpec.check "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize) = #[
    {
      target := { pp? := "mystery n + 1 = n + 2" },
      vars := #[{
         userName := "n",
         type? := .some { pp? := "Nat" },
      }],
    }
  ])

def test_capture_type_mismatch : TestT MetaM Unit := do
  let input := "
def mystery (k: Nat) : Nat := true
  "
  let options := { collectTypeErrors := true }
  let goalStates ← (collectSorrysFromSource input options).run' {}
  let [goalState] := goalStates | panic! s!"Incorrect number of states: {goalStates.length}"
  checkEq "goals" ((← goalState.serializeGoals).map (·.devolatilize)) #[
    {
      target := { pp? := "Nat" },
      vars := #[{
         userName := "k",
         type? := .some { pp? := "Nat" },
      }],
    }
  ]

def test_capture_type_mismatch_in_binder : TestT MetaM Unit := do
  let input := "
example (p: Prop) (h: (∀ (x: Prop), Nat) → p): p := h (λ (y: Nat) => 5)
  "
  let options := { collectTypeErrors := true }
  let goalStates ← (collectSorrysFromSource input options).run' {}
  let [goalState] := goalStates | panic! s!"Incorrect number of states: {goalStates.length}"
  checkEq "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize)) #[
  ]

def collectNewConstants (source: String) : MetaM (List (List Name)) := do
  let filename := "<anonymous>"
  let (context, state) ← do Frontend.createContextStateFromFile source filename (← getEnv) {}
  let m := Frontend.mapCompilationSteps λ step => do
    Frontend.collectNewDefinedConstants step
  m.run {} |>.run context |>.run' state

def test_collect_one_constant : TestT MetaM Unit := do
  let input := "
def mystery : Nat := 123
  "
  let names ← collectNewConstants input
  checkEq "constants" names [[`mystery]]
def test_collect_one_theorem : TestT MetaM Unit := do
  let input := "
theorem mystery [SizeOf α] (as : List α) (i : Fin as.length) : sizeOf (as.get i) < sizeOf as := by
  match as, i with
  | a::as, ⟨0, _⟩  => simp_arith [get]
  | a::as, ⟨i+1, h⟩ =>
    have ih := sizeOf_get as ⟨i, Nat.le_of_succ_le_succ h⟩
    apply Nat.lt_trans ih
    simp_arith
  "
  let names ← collectNewConstants input
  checkEq "constants" names [[`mystery]]

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("open", test_open),
    ("multiple_sorrys_in_proof", test_multiple_sorrys_in_proof),
    ("sorry in middle", test_sorry_in_middle),
    ("sorry in induction", test_sorry_in_induction),
    ("sorry in coupled", test_sorry_in_coupled),
    ("sorry with local instances", test_sorry_with_local_instance),
    ("environment_capture", test_environment_capture),
    ("capture_type_mismatch", test_capture_type_mismatch),
    --("capture_type_mismatch_in_binder", test_capture_type_mismatch_in_binder),
    ("collect_one_constant", test_collect_one_constant),
    ("collect_one_theorem", test_collect_one_theorem),
  ]
  tests.map (fun (name, test) => (name, runMetaMSeq env $ runTest test))

end Pantograph.Test.Frontend
