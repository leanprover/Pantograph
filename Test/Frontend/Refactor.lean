import Pantograph
import Test.Common

open Lean Pantograph Frontend

namespace Pantograph.Test.Frontend.Refactor

def suite (env : Environment): List (String × IO LSpec.TestSeq) :=
  let tests := [
  ]
  tests.map (fun (name, test) => (name, runMetaMSeq env $ runTest test))
