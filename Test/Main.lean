import Test.Delab
import Test.Environment
import Test.Frontend
import Test.Integration
import Test.Library
import Test.Metavar
import Test.Parser
import Test.Proofs
import Test.Serial
import Test.Tactic

import LSpec

-- Test running infrastructure

namespace Pantograph.Test

def addPrefix (pref: String) (tests: List (String × α)): List (String  × α) :=
  tests.map (λ (name, x) => (pref ++ "/" ++ name, x))

abbrev TestTask := Task (Except IO.Error LSpec.TestSeq)
def filterTestGroup (tests : List (String × IO LSpec.TestSeq)) (nameFilter? : Option String)
  : IO (List (String × TestTask)) := do
  let tests : List (String × IO LSpec.TestSeq) := match nameFilter? with
    | .some nameFilter => tests.filter (λ (name, _) => nameFilter.isPrefixOf name)
    | .none => tests
  tests.mapM λ (name, t) => return (name, ← IO.asTask t)

/-- Runs test in parallel. Filters test name if given -/
def runTestTask (t : (String × TestTask)) : IO LSpec.TestSeq := do
  let (name, task) := t
  let v: Except IO.Error LSpec.TestSeq := task.get
  return match v with
  | .ok case => LSpec.group name case
  | .error e => expectationFailure name e.toString

end Pantograph.Test

open Pantograph.Test

/-- Main entry of tests; Provide an argument to filter tests by prefix -/
def main (args: List String) := do
  let nameFilter? := args.head?
  Lean.initSearchPath (← Lean.findSysroot)
  let env_default : Lean.Environment ← Lean.importModules
    (imports := #[`Init])
    (opts := {})
    (trustLevel := 1)
    (loadExts := true)

  let suites: List (String × (Lean.Environment → List (String × IO LSpec.TestSeq))) := [
    ("Environment", Environment.suite),
    ("Frontend/Collect", Frontend.Collect.suite),
    ("Frontend/Distil", Frontend.Distil.suite),
    ("Frontend/Refactor", Frontend.Refactor.suite),
    ("Integration", Integration.suite),
    ("Library", Library.suite),
    ("Metavar", Metavar.suite),
    ("Parser", Parser.suite),
    ("Proofs", Proofs.suite),
    ("Delab", Delab.suite),
    ("Serial", Serial.suite),
    ("Tactic/Assign", Tactic.Assign.suite),
    ("Tactic/Fragment", Tactic.Fragment.suite),
    ("Tactic/Prograde", Tactic.Prograde.suite),
  ]
  let suiterunner (f : Lean.Environment → List (String × IO LSpec.TestSeq)) :=
    f env_default
  let tests : List (String × IO LSpec.TestSeq) := suites.foldl (init := []) λ acc (name, suite) =>
    acc ++ (addPrefix name $ suiterunner suite)
  LSpec.lspecEachIO (← filterTestGroup tests nameFilter?) runTestTask
