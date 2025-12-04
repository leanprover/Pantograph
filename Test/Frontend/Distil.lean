import Pantograph.Frontend
import Test.Common

open Lean Pantograph Frontend

namespace Pantograph.Test.Frontend.Distil

abbrev TestM := TestT MetaM
abbrev Test := TestM Unit

private def collectSorrysFromSource (source: String) (options : Frontend.GoalCollectionOptions := {})
    : CoreM (List GoalState) := do
  let (context, state) ← do Frontend.createContextStateFromFile source (env? := ← getEnv)
  let m := show FrontendM _ from Frontend.mapCompilationSteps λ step => do
    return (step.before, ← Frontend.collectSorrys step options)
  let li ← m.run {} |>.run context |>.run' state
  let goalStates ← li.filterMapM λ (env, sorrys) => withEnv env do
    if sorrys.isEmpty then
      return .none
    let { state, .. } ← (Frontend.sorrysToGoalState sorrys).run'
    return .some state
  return goalStates

private def test_sorry_in_middle: Test := do
  let sketch := "
example : ∀ (n m: Nat), n + m = m + n := by
  intros n m
  sorry
  "
  let goalStates ← collectSorrysFromSource sketch
  let [goalState] := goalStates | fail s!"Incorrect number of states: {goalStates.length}"
  checkEq "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize)) #[
    {
      target := { pp? := "n + m = m + n" },
      vars := #[{
           userName := `n,
           type? := .some { pp? := "Nat" },
        }, {
           userName := `m,
           type? := .some { pp? := "Nat" },
        }
      ],
    }
  ]
  let .success st _ ← runTermElabMInMeta $ goalState.tryDraft .unfocus "have : 1 + 1 = 2 := by sorry\nsorry"
    | fail "Draft tactic failed"
  checkEq "goals" st.goals.length 2

private def test_sorry_in_coupled: Test := do
  let sketch := "
example : ∀ (y: Nat), ∃ (x: Nat), y + 1 = x := by
  intro y
  apply Exists.intro
  case h => sorry
  case w => sorry
  "
  let goalStates ← collectSorrysFromSource sketch
  let [goalState] := goalStates | fail s!"Incorrect number of states: {goalStates.length}"
  checkEq "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize)) #[
    {
      target := { pp? := "y + 1 = ?w" },
      vars := #[{
           userName := `y,
           type? := .some { pp? := "Nat" },
        }
      ],
    },
    {
      userName? := .some `w,
      target := { pp? := "Nat" },
      vars := #[{
           userName := `y,
           type? := .some { pp? := "Nat" },
        }
      ],
    }
  ]

private def test_sorry_with_local_instance (tacticMode : Bool) : Test := do
  let placeholder := if tacticMode then "by sorry" else "sorry"
  let sketch := s!"
def test (α : Type) [s : Inhabited α] : α := @Inhabited.default α s
def mystery (α : Type) [Inhabited α] : α := {placeholder}
  "
  let goalStates ← collectSorrysFromSource sketch
  let [goalState] := goalStates | fail s!"Incorrect number of states: {goalStates.length}"
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

private def test_sorry_circular : Test := do
  let sketch := "
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by sorry
  "
  let goalStates ← collectSorrysFromSource sketch
  let [goalState] := goalStates | fail s!"Incorrect number of states: {goalStates.length}"
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

private def test_environment_capture: Test := do
  let sketch := "
def mystery (n: Nat) := n + 1

theorem about_mystery (n: Nat) : mystery n + 1 = n + 2 := sorry
  "
  let goalStates ← collectSorrysFromSource sketch
  let [goalState] := goalStates | fail s!"Incorrect number of states: {goalStates.length}"
  checkEq "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize)) #[
    {
      target := { pp? := "mystery n + 1 = n + 2" },
      vars := #[{
         userName := `n,
         type? := .some { pp? := "Nat" },
      }],
    }
  ]

private def test_capture_type_mismatch : Test := do
  let input := "
def mystery (k: Nat) : Nat := true
  "
  let options := { collectTypeErrors := true }
  let goalStates ← collectSorrysFromSource input options
  let [goalState] := goalStates | fail s!"Incorrect number of states: {goalStates.length}"
  checkEq "goals" ((← goalState.serializeGoals).map (·.devolatilize)) #[
    {
      target := { pp? := "Nat" },
      vars := #[{
         userName := `k,
         type? := .some { pp? := "Nat" },
      }],
    }
  ]

def test_capture_type_mismatch_in_binder : Test := do
  let input := "
theorem mystery (p: Prop) (h: (∀ (x: Prop), Nat) → p): p := h (λ (y: Nat) => 5)
  "
  let options := { collectTypeErrors := true }
  let goalStates ← collectSorrysFromSource input options
  let [goalState] := goalStates | fail s!"Incorrect number of states: {goalStates.length}"
  checkEq "goals" ((← goalState.serializeGoals (options := {})).map (·.devolatilize)) #[]

private def test_distil_simple : Test := do
  let input := "
set_option pp.analyze true
theorem mystery : ∀ (p q : Prop), p ∨ q → q ∨ p := sorry
  "
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input
    | fail "Incorrect number of search states"
  let .success state _ ← (state.tryTactic .unfocus "intro p q").run' (ctx := defaultElabContext)
    | fail "`intro` failed"
  checkEq "goals" state.goals.length 1

private def test_distil_tail : Test := do
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
           userName := `n,
           type? := .some { pp? := "Nat" },
        }, {
           userName := `m,
           type? := .some { pp? := "Nat" },
        }
      ],
    }]

private def test_distil_induction : Test := do
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
  let n' := .mkSimple "n✝"
  checkEq "start" ((← state.serializeGoals {}).map (·.devolatilize)) #[
    {
      target := { pp? := "n + 1 + m = m + (n + 1)" },
      vars := #[
        { var n' "Nat" with isInaccessible := true },
        var `m "Nat",
        var `n "Nat",
        var `ih "n + m = m + n",
        { var `h2 "n + m = m" with value? := .some { pp? := "?m.5" }},
      ],
    },
    {
      target := { pp? := "n + m = m" },
      vars := #[
        { var n' "Nat" with isInaccessible := true },
        var `m "Nat",
        var `n "Nat",
        var `ih "n + m = m + n",
      ],
    },
    {
      target := { pp? := "0 + m = m + 0" },
      vars := #[
        var `n "Nat",
        var `m "Nat",
        { var `h1 "0 + m = m" with value? := .some { pp? := "?m.2" }},
      ],
    },
    {
      target := { pp? := "0 + m = m" },
      vars := #[
        var `n "Nat",
        var `m "Nat",
      ],
    },
  ]
  where
  var (userName : Name) (type : String) : Protocol.Variable := {
    userName,
    type? := .some { pp? := type },
  }

private def test_distil_instance (tacticMode : Bool) : Test := do
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
          userName := `α,
          type? := .some { pp? := .some "Type" }
        },
        {
          userName := .mkSimple "inst✝",
          isInaccessible := true,
          type? := .some { pp? := .some "Inhabited α" }
        },
      ]
    }]
  let state? ← (state.tryTactic .unfocus "exact test α").run' (ctx := defaultElabContext)
  match state? with
  | .success state _ =>
    checkEq "goals" state.goals.length 0
    checkTrue "root" state.isSolved
  | .failure messages =>
    let messages ← messages.mapM (·.toString)
    checkEq "messages" messages #[];
    fail "failed"
  | .parseError e =>
    fail s!"Parse error: {e}"
  | .invalidAction e =>
    fail s!"Invalid action: {e}"

private def test_distil_environment_capture : Test := do
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
         userName := `n,
         type? := .some { pp? := "Nat" },
      }],
    }
  ]
  checkFalse "root" state.isSolved
  let .success state _ ← runTermElabMInMeta do state.tryTactic .unfocus "rfl"
    | fail "Tactic block failed"
  checkTrue "root" state.isSolved

private def test_distil_circular : Test := do
  let input := "
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by sorry
  "
  let id := "test"
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input
    | fail "Incorrect number of search states"
  let result ← (state.tryTactic .unfocus s!"exact {id} p q hp hq").run' (ctx := defaultElabContext)
  match result with
  | .success .. =>
    fail s!"This should not succeed"
  | .failure messages =>
    let messages ← messages.mapM (·.toString)
    checkEq "failure" messages #[s!"{← getFileName}:0:0: error(lean.unknownIdentifier): Unknown identifier `{id}`\n"]
  | .parseError e =>
    fail s!"Parse error: {e}"
  | .invalidAction e =>
    fail s!"Invalid action: {e}"

private def test_distil_companion : Test := do
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

private def test_distil_multiple_cond : Test := do
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

private def test_distil_existing_value : Test := do
  let input := "
def f : Nat → Nat := λ x => x + sorry
theorem mystery1 : f 1 = 2 := sorry
theorem mystery2 : f 2 = 4 := sorry
  "
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input { ignoreValues := false }
    | fail "Incorrect number of search states"
  checkEq "start" ((← state.serializeGoals {}).map (·.devolatilize))
    #[
      {
        userName? := `f,
        vars := #[{ userName := `x, type? := .some { pp? := .some "Nat" } }]
        target := { pp? := .some "Nat" },
      },
      {
        target := { pp? := .some "(fun x => x + ?f) 1 = 2" },
      },
      {
        target := { pp? := .some "(fun x => x + ?f) 2 = 4" },
      },
    ]
  checkFalse "root" state.isSolved
  let .success state _ ← runTermElabMInMeta do state.tryTactic .unfocus "exact x; rfl; rfl"
    | fail "Tactic block failed"
  checkEq "goals" state.goals.length 0
  checkTrue "root" state.isSolved

/-- Tests handling of newline chars -/
private def test_distil_predicate : Test := do
  let input := "
structure Command where
  prog : String
  args : List String

  deriving Repr, DecidableEq

def p (s : String) : Prop := s = \"ls\"

theorem mystery (s : String) : p s := sorry
  "
  let [_dst@{ goalState := state }] ← distilSearchTargets (← getEnv) input
    | fail "Incorrect number of search states"
  checkTrue "has `p" <| (state.env.find? `p).isSome
  let state? ← (state.tryDraft .unfocus "by\n  unfold p\n  sorry").run' (ctx := defaultElabContext)
  match state? with
  | .success state _ =>
    checkEq "goals" state.goals.length 1
  | .failure messages =>
    let messages ← messages.mapM (·.toString)
    checkEq "messages" messages #[];
    fail "failed"
  | .parseError e =>
    fail s!"Parse error: {e}"
  | .invalidAction e =>
    fail s!"Invalid action: {e}"


def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    --("sorry in middle", test_sorry_in_middle),
    --("sorry in coupled", test_sorry_in_coupled),
    --("sorry with local instances (term)", test_sorry_with_local_instance false),
    --("sorry with local instances (tactic)", test_sorry_with_local_instance true),
    --("sorry circular", test_sorry_circular),
    --("environment_capture", test_environment_capture),
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
    ("distil predicate", test_distil_predicate),
  ]
  tests.map (fun (name, test) => (name, runMetaMSeq env $ runTest test))
