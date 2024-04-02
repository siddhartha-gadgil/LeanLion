import Lake
open Lake DSL

package «LeanLion» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require LeanAideTools from git
  "https://github.com/siddhartha-gadgil/LeanAideTools.git"

@[default_target]
lean_lib «LeanLion» where
  -- add any library configuration options here
