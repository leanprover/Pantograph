import Pantograph
import Test.Common

open Lean Pantograph Frontend

namespace Pantograph.Test.Frontend.Collect

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


def collectNewConstants (source: String) : MetaM (List (List Name)) := do
  let filename := "<anonymous>"
  let (context, state) ← do Frontend.createContextStateFromFile source filename (← getEnv) {}
  let m := show FrontendM _ from Frontend.mapCompilationSteps λ step => do
    step.newConstants
  let result ← m.run {} |>.run context |>.run' state
  return result.map (·.toList)

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
def test_collect_stub : TestT MetaM Unit := do
  let input := "
theorem mystery [SizeOf α] (as : List α) (i : Fin as.length) : sizeOf (as.get i) < sizeOf as := sorry
  "
  let names ← collectNewConstants input
  checkEq "constants" names [[`mystery]]

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("open", test_open),
    ("collect_one_constant", test_collect_one_constant),
    ("collect_one_theorem", test_collect_one_theorem),
    ("collect_stub", test_collect_stub),
  ]
  tests.map (fun (name, test) => (name, runMetaMSeq env $ runTest test))
