import Pantograph
import Test.Common

open Lean Pantograph Frontend

namespace Pantograph.Test.Frontend.Refactor

abbrev Test := Environment → TestT IO Unit


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
  checkEq "result" result.trim expected

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("simple", test_refactor_simple),
  ]
  tests.map λ (name, test) => (name, runTest $ test env)
