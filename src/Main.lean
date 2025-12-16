import Common.Basic
-- Note: Individual section imports removed to avoid duplicate type definitions
-- Each section can be built independently: lake build TaxCode.SectionN

def main : IO Unit := do
  IO.println "US Tax Code Formalization - Lean 4"
  IO.println "See src/ for formal definitions"
  IO.println "Build individual sections with: lake build TaxCode.Section<N>"
