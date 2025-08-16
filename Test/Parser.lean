import LSpec
import Pantograph.Elab
import Test.Common

open Lean
namespace Pantograph.Test.Parser

abbrev TestM := TestT $ Elab.TermElabM

def test_runParserCategory : TestM Unit := do
  let .ok (stx, pos) := runParserCategory' (← getEnv) `tactic "intro n\ncases n"
    | fail "Tactic failed to parse"
  checkEq "stx" (toString stx.prettyPrint) "intro n"
  checkEq "pos" pos.byteIdx 8

def suite (env : Environment) : List (String × IO LSpec.TestSeq) :=
  [
    ("runParserCategory", test_runParserCategory),
  ] |>.map (λ (name, t) => (name, runTestTermElabM env t))
