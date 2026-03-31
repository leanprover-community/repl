import Lake
open Lake DSL

package dynlib where
  name := "dynlib"
  preferReleaseBuild := true

-- Define a target representing the prebuilt shared library
target mylib pkg : Dynlib := do pure $ Job.pure {
  path := pkg.sharedLibDir / nameToSharedLib "mylib"
  name := "mylib"
}

@[default_target]
lean_lib Dynlib where
  precompileModules := true
  moreLinkLibs := #[mylib]

lean_exe dynlib where
  root := `Main
  moreLinkLibs := #[mylib]
