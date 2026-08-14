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
  "https://github.com/argumentcomputer/LSpec.git" @ "3e23a4ad2e91eaf07845cecad157b7ffbb437aed"
lean_lib PantographTest {
}
@[test_driver]
lean_exe test {
  root := `PantographTest.Main
  -- Solves the native symbol not found problem
  supportInterpreter := true
}
