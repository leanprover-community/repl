import Lake
open Lake DSL

package dynlib where
  name := "dynlib"
  defaultTargets := #[`dynlib]

lean_lib Dynlib where
  -- no special settings needed

lean_exe dynlib where
  root := `Main
  moreLinkArgs := #["-Llib", "-lmylib"]
