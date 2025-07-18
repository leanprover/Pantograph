import Pantograph
import Test.Common

open Lean Pantograph Frontend

namespace Pantograph.Test.Frontend.Refactor

abbrev Test := Environment → TestT IO Unit

open Refactor in
def runRefactor (env : Environment) (source: String) (rContext : Refactor.Context := {})
  : IO String := do
  let filename := "<anonymous>"
  let (fContext, fState) ← createContextStateFromFile source filename env {}
  let m : RefactorM _ := do
    preprocessRefactor
    let f ← collectNextCommand
    return toString f
  m.run rContext |>.run' {}
    |>.run {}
    |>.run fContext |>.run' fState

example : Σ' f : Nat → Nat, ∀ (n : Nat), f n = n := by
  constructor
  intro n; rfl

private def test_refactor_simple : Test := λ env ↦ do
  let src := "
def f : Nat → Nat := sorry
theorem mystery (n : Nat) : f n = n := sorry
  "
  let expected := "
def f_composite : Σ' f : Nat → Nat, ∀ (n : Nat), f n = n := sorry
  ".trim
  let result ← runRefactor env src
  checkEq "result" result expected

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("simple", test_refactor_simple),
  ]
  tests.map λ (name, test) => (name, runTest $ test env)
