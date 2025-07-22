import Pantograph
import Test.Common

open Lean Pantograph Frontend

namespace Pantograph.Test.Frontend.Refactor

abbrev Test := Environment → TestT IO Unit

example : Σ' f : Nat → Nat, ∀ (n : Nat), f n = n := by
  constructor
  intro n; rfl

private def test_id : Test := λ env ↦ do
  let src := "
set_option pp.explicit true
open Nat in
def f : Nat → Nat := id
  "
  let expected := "
set_option pp.explicit true
open Nat in
def f : Nat → Nat :=
  id
  ".trim
  let result ← runRefactor env src
  checkEq "result" result.trim expected

private def test_simple : Test := λ env ↦ do
  let src := "
/-- S1 -/
def f : Nat → Nat := sorry
theorem mystery (n : Nat) : f n = n := sorry
  "
  let expected := "
/-- S1  -/
def f_composite : { f : Nat → Nat // ∀ (n : Nat), f n = n } :=
  sorry
  ".trim
  let result ← runRefactor env src
  checkEq "result" result.trim expected

private def test_invalid : Test := λ env ↦ do
  let src := "
/-- S1 -/
def f : Nat → Nat := sorry
theorem mystery (n : Nat) , f n = n := sorry
  "
  try
    let _ ← runRefactor env src
    fail "Should fail"
  catch ex : IO.Error =>
    checkEq "error" ex.toString Refactor.messageHasError

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("id", test_id),
    ("simple", test_simple),
    ("invalid", test_invalid),
  ]
  tests.map λ (name, test) => (name, runTest $ test env)
