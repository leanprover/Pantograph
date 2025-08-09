import Lake
open Lake DSL

package pantograph

lean_lib Pantograph {
  roots := #[`Pantograph]
  defaultFacets := #[LeanLib.sharedFacet]
}

lean_lib Repl {
}

@[default_target]
lean_exe repl {
  root := `Main
  -- Solves the native symbol not found problem
  supportInterpreter := true
}

lean_exe tomograph {
  root := `Tomograph
  -- Solves the native symbol not found problem
  supportInterpreter := true
}

require LSpec from git
  "https://github.com/argumentcomputer/LSpec.git" @ "db76512cd5266f0c576d561d8c69e2dc4890bea5"
lean_lib Test {
}
@[test_driver]
lean_exe test {
  root := `Test.Main
  -- Solves the native symbol not found problem
  supportInterpreter := true
}
