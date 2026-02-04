import Lake
open Lake DSL

package «Erdos347Param» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Erdos347Param» where
  -- add library configuration options here

lean_exe «erdos347param» where
  root := `Main
