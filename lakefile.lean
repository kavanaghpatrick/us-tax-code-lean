import Lake
open Lake DSL

package «us-tax-code» where
  srcDir := "src"

lean_lib «TaxCode» where
  roots := #[`TaxCode]

lean_lib «Common» where
  roots := #[`Common]

lean_lib «Utils» where
  roots := #[`Utils]

@[default_target]
lean_exe «us-tax-code» where
  root := `Main
