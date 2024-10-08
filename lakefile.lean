import Lake
open Lake DSL

package «proofnet» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"29dcec074de168ac2bf835a77ef68bbe069194c5"

@[default_target]
lean_lib «Proofnet» where
  globs := #[.submodules `Proofnet]

