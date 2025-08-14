import Pantograph.Frontend
import Test.Common

open Lean Pantograph Frontend

namespace Pantograph.Test.Frontend.Distil

private def collectSorrysFromSource (source: String) (options : Frontend.GoalCollectionOptions := {})
    : MetaM (List GoalState) := do
  let (context, state) ← do Frontend.createContextStateFromFile source (env? := ← getEnv)
  let m := show FrontendM _ from Frontend.mapCompilationSteps λ step => do
    return (step.before, ← Frontend.collectSorrys step options)
  let li ← m.run {} |>.run context |>.run' state
  let goalStates ← li.filterMapM λ (env, sorrys) => withEnv env do
    if sorrys.isEmpty then
      return .none
    let { state, .. } ← Frontend.sorrysToGoalState sorrys
    return .some state
  return goalStates

private def test_multiple_sorrys_in_proof : TestT MetaM Unit := do
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

private def test_sorry_in_middle: TestT MetaM Unit := do
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
  let .success st _ ← runTermElabMInMeta $ goalState.tryDraft .unfocus "have : 1 + 1 = 2 := by sorry\nsorry"
    | fail "Draft tactic failed"
  pure ()

private def test_sorry_in_induction : TestT MetaM Unit := do
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
    },
  ])

private def test_sorry_in_coupled: TestT MetaM Unit := do
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

private def test_sorry_with_local_instance (tacticMode : Bool) : TestT MetaM Unit := do
  let placeholder := if tacticMode then "by sorry" else "sorry"
  let sketch := s!"
def test (α : Type) [s : Inhabited α] : α := @Inhabited.default α s
example (α : Type) [Inhabited α] : α := {placeholder}
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

private def test_sorry_circular : TestT MetaM Unit := do
  let sketch := "
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by sorry
  "
  let goalStates ← (collectSorrysFromSource sketch).run' {}
  let [goalState] := goalStates | panic! s!"Incorrect number of states: {goalStates.length}"
  let result ← runTermElabMInMeta $ goalState.tryTactic .unfocus "exact test"
  checkTrue "failure" $ result matches .failure ..
  match result with
  | .success .. =>
    fail s!"This should not succeed"
  | .failure .. =>
    return ()
  | .parseError e =>
    fail s!"Parse error: {e}"
  | .invalidAction e =>
    fail s!"Invalid action: {e}"

private def test_environment_capture: TestT MetaM Unit := do
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

private def test_capture_type_mismatch : TestT MetaM Unit := do
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

private def test_distil_simple : TestT MetaM Unit := do
  let input := "
set_option pp.analyze true
theorem mystery : ∀ (p q : Prop), p ∨ q → q ∨ p := sorry
  "
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input
    | fail "Incorrect number of search states"
  let .success state _ ← (state.tryTactic .unfocus "intro p q").run' (ctx := defaultElabContext)
    | fail "`intro` failed"
  checkEq "goals" state.goals.length 1

private def test_distil_tail : TestT MetaM Unit := do
  let input := "
theorem mystery : ∀ (n m: Nat), n + m = m + n := by
  intros n m
  sorry
  "
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input { ignoreValues := false }
    | fail "Incorrect number of search states"
  checkEq "start" ((← state.serializeGoals {}).map (·.devolatilize))
    #[{
      target := { pp? := "n + m = m + n" },
      vars := #[{
           userName := "n",
           type? := .some { pp? := "Nat" },
        }, {
           userName := "m",
           type? := .some { pp? := "Nat" },
        }
      ],
    }]

private def test_distil_induction : TestT MetaM Unit := do
  let input := "
theorem mystery : ∀ (n m: Nat), n + m = m + n := by
  intros n m
  induction n with
  | zero =>
    have h1 : 0 + m = m := sorry
    sorry
  | succ n ih =>
    have h2 : n + m = m := sorry
    sorry
  "
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input { ignoreValues := false }
    | fail "Incorrect number of search states"
  checkEq "start" ((← state.serializeGoals {}).map (·.devolatilize)) #[
    {
      target := { pp? := "n + 1 + m = m + (n + 1)" },
      vars := #[
        { var "n✝" "Nat" with isInaccessible := true },
        var "m" "Nat",
        var "n" "Nat",
        var "ih" "n + m = m + n",
        var "h2" "n + m = m",
      ],
    },
    {
      target := { pp? := "n + m = m" },
      vars := #[
        { var "n✝" "Nat" with isInaccessible := true },
        var "m" "Nat",
        var "n" "Nat",
        var "ih" "n + m = m + n",
      ],
    },
    {
      target := { pp? := "0 + m = m + 0" },
      vars := #[
        var "n" "Nat",
        var "m" "Nat",
        var "h1" "0 + m = m",
      ],
    },
    {
      target := { pp? := "0 + m = m" },
      vars := #[
        var "n" "Nat",
        var "m" "Nat",
      ],
    },
  ]
  where
  var (userName type : String) : Protocol.Variable := {
    userName,
    type? := .some { pp? := type },
  }

private def test_distil_instance (tacticMode : Bool) : TestT MetaM Unit := do
  let placeholder := if tacticMode then "by sorry" else "sorry"
  let input := s!"
def test (α : Type) [s : Inhabited α] : α := @Inhabited.default α s
def mystery (α : Type) [Inhabited α] : α := {placeholder}
  "
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input { ignoreValues := false }
    | fail "Incorrect number of search states"
  checkEq "start" ((← state.serializeGoals {}).map (·.devolatilize))
    #[{
      target := { pp? := .some "α" },
      vars := #[
        {
          userName := "α",
          type? := .some { pp? := .some "Type" }
        },
        {
          userName := "inst✝",
          isInaccessible := true,
          type? := .some { pp? := .some "Inhabited α" }
        },
      ]
    }]
  let state? ← (state.tryTactic .unfocus "exact test α").run' (ctx := defaultElabContext)
  match state? with
  | .success state _ =>
    checkEq "goals" state.goals.length 0
  | .failure messages =>
    let messages ← messages.mapM (·.toString)
    checkEq "messages" messages #[];
    fail "failed"
  | .parseError e =>
    fail s!"Parse error: {e}"
  | .invalidAction e =>
    fail s!"Invalid action: {e}"

private def test_distil_environment_capture : TestT MetaM Unit := do
  let input := "
def mystery (n: Nat) := n + 1

theorem property (n: Nat) : mystery n + 1 = n + 2 := sorry
  "
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input { ignoreValues := false }
    | fail "Incorrect number of search states"
  let goals := (← state.serializeGoals).map (·.devolatilize)
  checkEq "goals" goals #[
    {
      target := { pp? := "mystery n + 1 = n + 2" },
      vars := #[{
         userName := "n",
         type? := .some { pp? := "Nat" },
      }],
    }
  ]

private def test_distil_circular : TestT MetaM Unit := do
  let input := "
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by sorry
  "
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input
    | fail "Incorrect number of search states"
  let result ← (state.tryTactic .unfocus "exact test p q hp hq").run' (ctx := defaultElabContext)
  match result with
  | .success .. =>
    fail s!"This should not succeed"
  | .failure messages =>
    let fileName ← getFileName
    let messages ← messages.mapM (·.toString)
    checkEq "failure" messages #[s!"{fileName}:0:0: error: unknown identifier 'test'\n"]
  | .parseError e =>
    fail s!"Parse error: {e}"
  | .invalidAction e =>
    fail s!"Invalid action: {e}"

private def test_distil_companion : TestT MetaM Unit := do
  let input := "
def f : Nat → Nat := sorry
def g : Nat → Nat := λ x => x + 1
theorem mystery (n : Nat) : f n = g n := sorry
  "
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input
    | fail "Incorrect number of search states"
  checkEq "start" ((← state.serializeGoals {}).map (·.devolatilize))
    #[{
      target := { pp? := .some "{ f // ∀ (n : Nat), f n = g n }" },
    }]

private def test_distil_multiple_cond : TestT MetaM Unit := do
  let input := "
def f : Nat → Nat := sorry
theorem mystery1 : f 1 = 1 := sorry
theorem mystery2 : f 2 = 2 := sorry
  "
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input
    | fail "Incorrect number of search states"
  checkEq "start" ((← state.serializeGoals {}).map (·.devolatilize))
    #[{
      target := { pp? := .some "{ f // f 1 = 1 ∧ f 2 = 2 }" },
    }]

private def test_distil_existing_value : TestT MetaM Unit := do
  let input := "
def f : Nat → Nat := λ x => x + sorry
theorem mystery1 : f 1 = 1 := sorry
theorem mystery2 : f 2 = 2 := sorry
  "
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input { ignoreValues := false }
    | fail "Incorrect number of search states"
  checkEq "start" ((← state.serializeGoals {}).map (·.devolatilize))
    #[
      {
        vars := #[{ userName := "x", type? := .some { pp? := .some "Nat" } }]
        target := { pp? := .some "Nat" },
      },
      {
        target := { pp? := .some "(fun x => x + ?m.7) 1 = 1" },
      },
      {
        target := { pp? := .some "(fun x => x + ?m.7) 2 = 2" },
      },
    ]

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("multiple_sorrys_in_proof", test_multiple_sorrys_in_proof),
    ("sorry in middle", test_sorry_in_middle),
    ("sorry in induction", test_sorry_in_induction),
    ("sorry in coupled", test_sorry_in_coupled),
    ("sorry with local instances (term)", test_sorry_with_local_instance false),
    ("sorry with local instances (tactic)", test_sorry_with_local_instance true),
    ("sorry circular", test_sorry_circular),
    ("environment_capture", test_environment_capture),
    ("capture_type_mismatch", test_capture_type_mismatch),
    --("capture_type_mismatch_in_binder", test_capture_type_mismatch_in_binder),
    ("distil simple", test_distil_simple),
    ("distil tail", test_distil_tail),
    ("distil induction", test_distil_induction),
    ("distil instance (term)", test_distil_instance false),
    ("distil instance (true)", test_distil_instance true),
    ("distil environment capture", test_distil_environment_capture),
    ("distil circular", test_distil_circular),
    ("distil companion", test_distil_companion),
    ("distil multiple conditions", test_distil_multiple_cond),
    ("distil existing value", test_distil_existing_value),
  ]
  tests.map (fun (name, test) => (name, runMetaMSeq env $ runTest test))
