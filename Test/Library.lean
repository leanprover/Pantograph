import LSpec
import Lean
import Pantograph.Library
import Test.Common

open Lean
open Pantograph

namespace Pantograph.Test.Library

def runTermElabM { α } (termElabM: Elab.TermElabM α): CoreM α :=
  termElabM.run' (ctx := defaultElabContext) |>.run'

def test_expr_echo (env: Environment): IO LSpec.TestSeq := do
  let inner: CoreM LSpec.TestSeq := do
    let prop_and_proof := "⟨∀ (x: Prop), x → x, λ (x: Prop) (h: x) => h⟩"
    let tests := LSpec.TestSeq.done
    let echoResult ← runTermElabM $ exprEcho prop_and_proof (options := {})
    let tests := tests.append (LSpec.test "fail" (echoResult.toOption == .some {
      type := { pp? := "?m.2" }, expr := { pp? := "?m.3" }
    }))
    let echoResult ← runTermElabM $ exprEcho prop_and_proof (expectedType? := .some "Σ' p:Prop, p") (options := { printExprAST := true })
    let tests := tests.append (LSpec.test "fail" (echoResult.toOption == .some {
      type := {
        pp? := "(p : Prop) ×' p",
        sexp? := "((:c PSigma) (:sort 0) (:lambda p (:sort 0) 0))",
      },
      expr := {
        pp? := "⟨∀ (x : Prop), x → x, fun x h => h⟩",
        sexp? := "((:c PSigma.mk) (:sort 0) (:lambda p (:sort 0) 0) (:forall x (:sort 0) (:forall a 0 1)) (:lambda x (:sort 0) (:lambda h 0 0)))",
      }
    }))
    return tests
  runCoreMSeq env (options := #["pp.proofs.threshold=100"]) inner

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("expr_echo", test_expr_echo env),
  ]
