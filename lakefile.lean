import Lake
open Lake DSL

package «us-tax-code» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- Shared common definitions
lean_lib «Common» where
  srcDir := "src"

-- Section1 is standalone (defines its own types)
lean_lib «TaxCode» where
  srcDir := "src"
  globs := #[.submodules `TaxCode]
