import Lake
open Lake DSL

package setTheory {
  -- add package configuration options here
}

lean_lib SetTheory {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe setThoery {
  root := `Main
}
