import Pantograph.Frontend
import Pantograph.Environment
import Test.Common

open Lean Pantograph Frontend

namespace Pantograph.Test.Frontend.Collect

abbrev Test := Environment → TestT IO Unit

def runFrontend { α } (env : Environment) (source: String) (f : CompilationStep → FrontendM α) (timeout : UInt32 := 0)
  : IO (List α) := do
  let filename := "<anonymous>"
  let (context, state) ← do createContextStateFromFile source filename env {}
  let m := mapCompilationSteps f
  let cancelTk? ← match timeout with
    | 0 => pure .none
    | timeout => .some <$> spawnCancelToken timeout
  m.run { cancelTk? } |>.run context |>.run' state

def test_open : Test := λ env => do
  let sketch := "
open Nat
example : ∀ (n : Nat), n + 1 = Nat.succ n := by
  intro
  apply add_one
  "
  let errors ← runFrontend env sketch λ step => step.msgs.mapM (·.toString)
  checkEq "errors" errors [[], []]

def collectNewConstants (env : Environment) (source: String) : IO (List (List Name)) := do
  let filename := "<anonymous>"
  let (context, state) ← do Frontend.createContextStateFromFile source filename env {}
  let m := show FrontendM _ from Frontend.mapCompilationSteps λ step => do
    step.newConstants
  let result ← m.run {} |>.run context |>.run' state
  return result.map (·.toList)

def test_collect_one_constant : Test := λ env => do
  let input := "
def mystery : Nat := 123
  "
  let names ← collectNewConstants env input
  checkEq "constants" names [[`mystery]]

def test_collect_one_theorem : Test := λ env => do
  let input := "
theorem mystery [SizeOf α] (as : List α) (i : Fin as.length) : sizeOf (as.get i) < sizeOf as := by
  match as, i with
  | a::as, ⟨0, _⟩  => simp_arith [get]
  | a::as, ⟨i+1, h⟩ =>
    have ih := sizeOf_get as ⟨i, Nat.le_of_succ_le_succ h⟩
    apply Nat.lt_trans ih
    simp_arith
  "
  let names ← collectNewConstants env input
  checkEq "constants" names [[`mystery]]

def test_collect_stub : Test := λ env => do
  let input := "
theorem mystery [SizeOf α] (as : List α) (i : Fin as.length) : sizeOf (as.get i) < sizeOf as := sorry
  "
  let names ← collectNewConstants env input
  checkEq "constants" names [[`mystery]]

def checkFileConflicts (env : Environment) (src dst : String) : IO (Except String Environment):= do
  let srcEnv ← collectOne src
  let dstEnv ← collectOne dst
  ExceptT.run $ Environment.checkConflicts env srcEnv dstEnv
  where
  collectOne (source : String) : IO Environment := do
    let filename := "<anonymous>"
    let (context, state) ← do createContextStateFromFile source filename env {}
    let m := collectEndEnvironment
    m.run { } |>.run context |>.run' state

def test_conflict_simple : Test := λ env => do
  let src := "
def x : Nat := sorry
  "
  let dst := "
def x : Nat := 123
  "
  let result? ← checkFileConflicts env src dst
  match result? with
  | .ok _ =>  checkTrue "ok" result?.isOk
  | .error e =>  fail s!"Failed with {e}"

def test_conflict_auxiliary : Test := λ env => do
  let src := "
def f : Nat → Nat := sorry
  "
  let dst := "
def x : Nat := 123
def f : Nat → Nat := λ y => y + x
  "
  let result? ← checkFileConflicts env src dst
  match result? with
  | .ok _ =>  checkTrue "ok" result?.isOk
  | .error e =>  fail s!"Failed with {e}"

/-- from `GasStationManager/SafeVerify` -/
def test_conflict_simple_def : Test := λ env => do
  let src := "
def solveAdd (a b:Int):{c:Int//a+c=b} := sorry
  "
  let dst := "
def solveAdd (a b:Int):{c:Int//a+c=b} := ⟨b-a, by omega⟩
  "
  let result? ← checkFileConflicts env src dst
  match result? with
  | .ok _ =>  checkTrue "ok" result?.isOk
  | .error e =>  fail s!"Failed with {e}"
/-- from `GasStationManager/SafeVerify` -/
def test_conflict_fake_implementation : Test := λ env => do
  let src := "
noncomputable def definitely_at_least_two : Nat := sorry
theorem definitely_at_least_two_spec : 2 ≤ definitely_at_least_two := sorry
  "
  let dst := "
@[implemented_by Nat.zero]
noncomputable def definitely_at_least_two : Nat :=
  Exists.choose (⟨3, by simp⟩ : ∃ x, 2 ≤ x)

theorem definitely_at_least_two_spec : 2 ≤ definitely_at_least_two :=
  Exists.choose_spec _
  "
  let result? ← checkFileConflicts env src dst
  match result? with
  | .ok _ =>  checkTrue "ok" result?.isOk
  | .error e =>  fail s!"Failed with {e}"

def test_conflict_fail_idempotent : Test := λ env => do
  let src := "
def x : Nat := sorry
  "
  let .error e ← checkFileConflicts env src src
    | fail "Must fail"
  checkEq "message" e "Definition value has sorry: x._cstage1"

def test_conflict_fail_inductive_modification : Test := λ env => do
  let src := "
inductive A where
  | a
  | b
  "
  let dst := "
inductive A where
  | a
  | b
  | c
  "
  let .error e ← checkFileConflicts env src dst
    | fail "Must fail"
  checkEq "message" e "Type clash of A.casesOn"

/-- from `GasStationManager/SafeVerify` -/
def test_conflict_fail_noncomputable : Test := λ env => do
  let src := "
axiom α : Type
axiom ne : Nonempty α
def f : α := sorry
  "
  let dst := "
axiom α : Type
axiom ne : Nonempty α
noncomputable def f : α := @Classical.choice α ne
  "
  let .error e ← checkFileConflicts env src dst
    | fail "Must fail"
  checkEq "message" e "Must not modify computability on f"

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("open", test_open),
    ("collect_one_constant", test_collect_one_constant),
    ("collect_one_theorem", test_collect_one_theorem),
    ("collect_stub", test_collect_stub),
    ("conflict simple", test_conflict_simple),
    ("conflict auxiliary", test_conflict_auxiliary),
    ("conflict simple def", test_conflict_simple_def),
    ("conflict fake implementation", test_conflict_fake_implementation),
    ("conflict fail idempotent", test_conflict_fail_idempotent),
    ("conflict fail inductive modification", test_conflict_fail_inductive_modification),
    ("conflict fail noncomputable", test_conflict_fail_noncomputable),
  ]
  tests.map (fun (name, test) => (name, runTest $ test env))
