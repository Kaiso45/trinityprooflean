import Lake
open Lake DSL

package trinity where
  moreLeanArgs := #["-DautoImplicit=true"]
  require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.3.0"

@[default_target]
lean_lib TrinitySpanModel

@[test_driver]
lean_exe tests where
  root := `Test
