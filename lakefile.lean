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
  "https://github.com/argumentcomputer/LSpec.git" @ "ab4d5eb461941837f48eb891be755c8c73e89fdd"
lean_lib PantographTest {
}
@[test_driver]
lean_exe test {
  root := `PantographTest.Main
  -- Solves the native symbol not found problem
  supportInterpreter := true
}
