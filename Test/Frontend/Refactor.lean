import Pantograph
import Test.Common

open Lean Pantograph Frontend

namespace Pantograph.Test.Frontend.Refactor

abbrev Test := Environment → TestT IO Unit

example : Σ' f : Nat → Nat, ∀ (n : Nat), f n = n := by
  constructor
  intro n; rfl

private def test_simple : Test := λ env ↦ do
  let src := "
/-- S1 -/
def f : Nat → Nat := sorry
theorem mystery (n : Nat) : f n = n := sorry
  "
  let expected := "
/-- S1  -/
def f_composite : { binderName : Nat → Nat // ∀ (n : Nat), binderName n = n } :=
  sorry
  ".trim
  let result ← runRefactor env src
  checkEq "result" result.trim expected

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("simple", test_simple),
  ]
  tests.map λ (name, test) => (name, runTest $ test env)
