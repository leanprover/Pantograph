import Test.Delate
import Test.Environment
import Test.Frontend
import Test.Integration
import Test.Library
import Test.Metavar
import Test.Proofs
import Test.Serial
import Test.Tactic

import LSpec

-- Test running infrastructure

namespace Pantograph.Test

def addPrefix (pref: String) (tests: List (String × α)): List (String  × α) :=
  tests.map (λ (name, x) => (pref ++ "/" ++ name, x))

/-- Runs test in parallel. Filters test name if given -/
def runTestGroup (nameFilter?: Option String) (tests: List (String × IO LSpec.TestSeq)): IO LSpec.TestSeq := do
  let tests: List (String × IO LSpec.TestSeq) := match nameFilter? with
    | .some nameFilter => tests.filter (λ (name, _) => nameFilter.isPrefixOf name)
    | .none => tests
  let tasks: List (String × Task _) ← tests.mapM (λ (name, task) => do
    return (name, ← EIO.asTask task))
  let all := tasks.foldl (λ acc (name, task) =>
    let v: Except IO.Error LSpec.TestSeq := Task.get task
    match v with
    | .ok case => acc ++ (LSpec.group name case)
    | .error e => acc ++ (expectationFailure name e.toString)
    ) LSpec.TestSeq.done
  return all

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
    ("Frontend", Frontend.suite),
    ("Integration", Integration.suite),
    ("Library", Library.suite),
    ("Metavar", Metavar.suite),
    ("Proofs", Proofs.suite),
    ("Delate", Delate.suite),
    ("Serial", Serial.suite),
    ("Tactic/Assign", Tactic.Assign.suite),
    ("Tactic/Fragment", Tactic.Fragment.suite),
    ("Tactic/Prograde", Tactic.Prograde.suite),
    ("Tactic/Special", Tactic.Special.suite),
  ]
  let suiterunner (f : Lean.Environment → List (String × IO LSpec.TestSeq)) :=
    f env_default
  let tests : List (String × IO LSpec.TestSeq) := suites.foldl (init := []) λ acc (name, suite) =>
    acc ++ (addPrefix name $ suiterunner suite)
  LSpec.lspecEachIO [()] (λ () => runTestGroup nameFilter? tests)
