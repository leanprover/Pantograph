import Pantograph
import Test.Common

open Lean Pantograph Frontend

namespace Pantograph.Test.Frontend.Refactor

abbrev Test := Environment → TestT IO Unit

deriving instance Repr, DecidableEq for FileMap

private def test_merge_file_map : Test := λ _env ↦ do
  let src1 := "
set_option pp.explicit true
open Nat in
def f : Nat → Nat := id
  ".trimAscii.toString
  let src2 := "
set_option pp.explicit true
open Nat in
def f : Nat → Nat :=
  id
  ".trimAscii.toString
  let filemap1 := s!"{src1}\n{src2}".toFileMap
  let filemap2 := Refactor.mergeFileMap src1.toFileMap src2.toFileMap
  checkEq "result" filemap1 filemap2

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
  ".trimAscii.toString
  let result ← runRefactor env src
  checkEq "result" result.trimAscii.toString expected

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
  ".trimAscii.toString
  let result ← runRefactor env src
  checkEq "result" result.trimAscii.toString expected

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
    checkEq "error" ex.toString s!"{defaultFileName}:4:25: error: unexpected token ','; expected ':'\n"

private def test_intercalating : Test := λ env ↦ do
  let src := "
def f : Nat → Nat := sorry
def helper (n : Nat) : Nat := n + 1
theorem mystery (n : Nat) : f n = helper n := sorry
  "
  let expected := "
def helper (n : Nat) : Nat :=
  n + 1
def f_composite : { f : Nat → Nat // ∀ (n : Nat), f n = helper n } :=
  sorry
  ".trimAscii.toString
  let result ← runRefactor env src
  checkEq "result" result.trimAscii.toString expected

private def test_predicate : Test := λ env ↦ do
  let src := "
def q : (Nat → Nat) → Prop := sorry
def p : (Nat → Nat) → Prop := sorry
theorem mystery : p Nat.succ := sorry
  "
  let expected := "
def q : (Nat → Nat) → Prop :=
  sorry
def p_composite : { p : (Nat → Nat) → Prop // p Nat.succ } :=
  sorry
  ".trimAscii.toString
  let result ← runRefactor env src
  checkEq "result" result.trimAscii.toString expected

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
    ("merge file map", test_merge_file_map),
    ("id", test_id),
    ("simple", test_simple),
    ("invalid", test_invalid),
    ("intercalating", test_intercalating),
    ("predicate", test_predicate),
  ]
  tests.map λ (name, test) => (name, runTest $ test env)
