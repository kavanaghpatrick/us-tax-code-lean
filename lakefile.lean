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

lean_lib «Tests» where
  roots := #[`Tests]
  globs := #[.submodules `Tests]

@[default_target]
lean_exe «us-tax-code» where
  root := `Main
