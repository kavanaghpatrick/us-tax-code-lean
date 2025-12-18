
/-!
## Threshold Boundary Tests
Testing behavior at exact threshold values.
-/

import Mathlib
import TaxCode.Section453
import TaxCode.Section951_956

set_option linter.unusedVariables false
noncomputable section

open Section453 in
/-!
## §453 Installment Sale $5M Threshold
-/

def saleAt5M : InstallmentSale := {
  sellingPrice := 5000000  -- Exactly $5M
  adjustedBasis := 1000000
  propertyType := .RealProperty
  saleYear := ⟨2024, by omega⟩
  yearOfSalePayment := 1000000
  subsequentPayments := [(⟨2025, by omega⟩, 2000000), (⟨2026, by omega⟩, 2000000)]
  isRelatedPartySale := false
  buyerId := 1
  sellerId := 2
}

def saleAt5M_plus1 : InstallmentSale := {
  sellingPrice := 5000001  -- $5M + $1
  adjustedBasis := 1000000
  propertyType := .RealProperty
  saleYear := ⟨2024, by omega⟩
  yearOfSalePayment := 1000000
  subsequentPayments := [(⟨2025, by omega⟩, 2000000), (⟨2026, by omega⟩, 2000001)]
  isRelatedPartySale := false
  buyerId := 1
  sellerId := 2
}

def saleAt4_999_999 : InstallmentSale := {
  sellingPrice := 4999999  -- $5M - $1
  adjustedBasis := 1000000
  propertyType := .RealProperty
  saleYear := ⟨2024, by omega⟩
  yearOfSalePayment := 999999
  subsequentPayments := [(⟨2025, by omega⟩, 2000000), (⟨2026, by omega⟩, 2000000)]
  isRelatedPartySale := false
  buyerId := 1
  sellerId := 2
}

#eval! isLargeInstallmentSale saleAt4_999_999  -- false
#eval! isLargeInstallmentSale saleAt5M         -- false (not GREATER than)
#eval! isLargeInstallmentSale saleAt5M_plus1   -- true ($1 over triggers!)

-- Interest charge kicks in at $5M+
-- Cliff effect: $5,000,000 = no interest, $5,000,001 = interest on ALL deferred tax

open Section951_956 in
/-!
## §951A High Tax Exception (18.9% threshold)
-/

-- US corporate rate is 21%, high-tax threshold is 90% of that = 18.9%
#eval! usCorpTaxRate      -- 21/100
#eval! highTaxThreshold   -- 90/100 * 21/100 = 18.9/100

-- Test at boundaries
#eval! qualifiesForHighTaxException (18/100)   -- false (18% < 18.9%)
#eval! qualifiesForHighTaxException (189/1000) -- false (18.9% = 18.9%, need GREATER)
#eval! qualifiesForHighTaxException (19/100)   -- true (19% > 18.9%)
#eval! qualifiesForHighTaxException (20/100)   -- true

-- Ireland at 12.5%
#eval! qualifiesForHighTaxException (125/1000) -- false (12.5% < 18.9%)

-- Japan at 30%
#eval! qualifiesForHighTaxException (30/100)   -- true (30% > 18.9%)

end
