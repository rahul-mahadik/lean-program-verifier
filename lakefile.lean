import Lake
open Lake DSL

package miniVerify

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84"

@[default_target]
lean_lib MiniVerify

lean_exe miniverify where
  root := `Main
