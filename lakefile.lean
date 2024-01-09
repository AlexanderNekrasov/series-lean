import Lake
open Lake DSL

package «series-lean» where
  -- add package configuration options here

lean_lib «SeriesLean» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"


@[default_target]
lean_exe «series-lean» where
  root := `Main
