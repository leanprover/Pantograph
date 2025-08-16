import Lean.Meta
import Lean.Elab
import LSpec
import Test.Common

open Lean

namespace Pantograph.Test.Tactic.Assign

def test_draft : TestT Elab.TermElabM Unit := do
  let expr := "forall (p : Prop), (p ∨ p) ∨ p"
  let skeleton := "by\nhave a : p ∨ p := sorry\nsorry"
  let expr ← parseSentence expr
  Meta.forallTelescope expr $ λ _ body => do
    let skeleton' ← match Parser.runParserCategory
      (env := ← MonadEnv.getEnv)
      (catName := `term)
      (input := skeleton)
      (fileName := ← getFileName) with
      | .ok syn => pure syn
      | .error error => throwError "Failed to parse: {error}"
    -- Apply the tactic
    let target ← Meta.mkFreshExprSyntheticOpaqueMVar body
    let tactic := Tactic.evalDraft skeleton'
    let newGoals ← runTacticOnMVar tactic target.mvarId!
    addTest $ LSpec.check "goals" ((← newGoals.mapM (λ g => do exprToStr (← g.getType))) = ["p ∨ p", "(p ∨ p) ∨ p"])

def suite (env: Environment): List (String × IO LSpec.TestSeq) :=
  [
    ("draft", test_draft),
  ] |>.map (λ (name, t) => (name, runTestTermElabM env t))
