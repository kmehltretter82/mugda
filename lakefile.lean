import Lake
open Lake DSL

package mugda where
  version := v!"1.0.0"

@[default_target]
lean_lib Mugda where
  roots := #[`Mugda]

@[default_target]
lean_exe mugda where
  root := `Main
