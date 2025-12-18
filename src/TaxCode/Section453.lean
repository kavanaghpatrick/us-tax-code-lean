/-
IRC Section 453 - Installment Method

The installment method allows taxpayers to defer gain recognition on sales
where at least one payment is received after the tax year of sale.

Key loophole mechanics:
- Defer gain recognition over payment period
- Gross profit ratio determines taxable portion of each payment
- Interest charge on large installment sales ($5M+ threshold)
- Related party disposition rules (2-year holding requirement)
- Contingent payment sales (maximum selling price issues)
-/

import Mathlib

set_option linter.unusedVariables false

noncomputable section

-- Use Int directly as Currency
abbrev Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

/-!
## §453(a) - General Rule

Installment method applies automatically to qualifying sales.
Income is recognized proportionally as payments are received.
-/

-- Threshold for interest charge under §453A
def installmentThreshold : Currency := 5000000

-- Related party holding period
def relatedPartyHoldingPeriod : Nat := 2  -- years

/-!
## Sale Structure
-/

inductive PropertyType where
  | RealProperty
  | PersonalProperty
  | DealerProperty  -- §453(b)(2) - dealers can't use installment
  | PubliclyTradedProperty  -- §453(k) - can't use installment
  | DepreciableProperty  -- §453(i) - special rules
  deriving DecidableEq, Repr

structure InstallmentSale where
  sellingPrice : Currency
  adjustedBasis : Currency
  propertyType : PropertyType
  saleYear : TaxYear
  yearOfSalePayment : Currency  -- Payment received in year of sale
  subsequentPayments : List (TaxYear × Currency)  -- (Year, Amount)
  isRelatedPartySale : Bool
  buyerId : Nat
  sellerId : Nat
  deriving Repr

/-!
## §453(c) - Installment Sale Defined

A sale where at least one payment is received after the tax year of sale.
-/

def isInstallmentSale (sale : InstallmentSale) : Bool :=
  sale.subsequentPayments.length > 0

-- §453(b)(2) - Dealer dispositions don't qualify
-- §453(k) - Publicly traded property doesn't qualify
def qualifiesForInstallmentMethod (sale : InstallmentSale) : Bool :=
  isInstallmentSale sale &&
  sale.propertyType ≠ .DealerProperty &&
  sale.propertyType ≠ .PubliclyTradedProperty

/-!
## §453(c) - Gross Profit and Gross Profit Ratio

The key formula for installment method taxation.
-/

def grossProfit (sale : InstallmentSale) : Currency :=
  sale.sellingPrice - sale.adjustedBasis

def grossProfitRatio (sale : InstallmentSale) : Rat :=
  if sale.sellingPrice = 0 then 0
  else grossProfit sale / sale.sellingPrice

-- Gain recognized on each payment
def gainFromPayment (sale : InstallmentSale) (payment : Currency) : Currency :=
  Int.floor (grossProfitRatio sale * payment)

/-!
## Total Payments and Gain Tracking
-/

def totalPayments (sale : InstallmentSale) : Currency :=
  sale.yearOfSalePayment +
  sale.subsequentPayments.foldl (fun acc (_, amt) => acc + amt) 0

def gainInYearOfSale (sale : InstallmentSale) : Currency :=
  gainFromPayment sale sale.yearOfSalePayment

def gainInYear (sale : InstallmentSale) (year : TaxYear) : Currency :=
  if year = sale.saleYear then
    gainInYearOfSale sale
  else
    sale.subsequentPayments.foldl (fun acc (y, amt) =>
      if y = year then acc + gainFromPayment sale amt else acc
    ) 0

-- Total gain recognized across all years
def totalGainRecognized (sale : InstallmentSale) : Currency :=
  gainInYearOfSale sale +
  sale.subsequentPayments.foldl (fun acc (_, amt) =>
    acc + gainFromPayment sale amt
  ) 0

/-!
## §453A - Interest on Deferred Tax on Large Installment Sales

For sales over $5M, interest is charged on the deferred tax.
-/

def isLargeInstallmentSale (sale : InstallmentSale) : Bool :=
  sale.sellingPrice > installmentThreshold

-- Outstanding installment obligations at end of year
def outstandingObligation (sale : InstallmentSale) (afterYear : TaxYear) : Currency :=
  sale.subsequentPayments.foldl (fun acc (y, amt) =>
    if y.year > afterYear.year then acc + amt else acc
  ) 0

-- Deferred gain = outstanding obligation × gross profit ratio
def deferredGain (sale : InstallmentSale) (afterYear : TaxYear) : Currency :=
  Int.floor (grossProfitRatio sale * outstandingObligation sale afterYear)

-- Interest charge on deferred tax (simplified - actual uses applicable rate)
def interestOnDeferredTax (sale : InstallmentSale) (afterYear : TaxYear)
    (taxRate : Rat) (interestRate : Rat) : Currency :=
  if isLargeInstallmentSale sale then
    let deferred := deferredGain sale afterYear
    let deferredTax := Int.floor (taxRate * deferred)
    Int.floor (interestRate * deferredTax)
  else 0

/-!
## §453(e) - Related Party Sales

If property is sold to a related party who then resells within 2 years,
the original seller recognizes gain on the resale.
-/

structure Resale where
  originalSale : InstallmentSale
  resaleDate : TaxYear
  resaleProceeds : Currency
  deriving Repr

def yearsFromOriginalSale (sale : InstallmentSale) (resale : Resale) : Nat :=
  resale.resaleDate.year - sale.saleYear.year

def triggersRelatedPartyRule (sale : InstallmentSale) (resale : Resale) : Bool :=
  sale.isRelatedPartySale &&
  yearsFromOriginalSale sale resale < relatedPartyHoldingPeriod

-- Gain accelerated to original seller
def acceleratedGain (sale : InstallmentSale) (resale : Resale) : Currency :=
  if triggersRelatedPartyRule sale resale then
    -- Original seller recognizes remaining deferred gain
    let recognized := gainInYearOfSale sale
    grossProfit sale - recognized
  else 0

/-!
## §453(i) - Depreciation Recapture

Ordinary income recapture (§1245/1250) is recognized in year of sale,
not deferred under installment method.
-/

structure DepreciationRecapture where
  section1245Recapture : Currency  -- Ordinary income
  section1250Recapture : Currency  -- Unrecaptured §1250 gain
  deriving Repr

def gainInYearOfSaleWithRecapture (sale : InstallmentSale)
    (recapture : DepreciationRecapture) : Currency :=
  -- Recapture is recognized immediately, not deferred
  recapture.section1245Recapture +
  recapture.section1250Recapture +
  gainInYearOfSale sale

/-!
## §453(j) - Contingent Payment Sales

When selling price is contingent, special rules apply.
-/

inductive ContingentSaleType where
  | StatedMaximum  -- Maximum price stated
  | FixedPeriod    -- Maximum period for payments
  | Neither        -- Neither stated - basis recovery method
  deriving DecidableEq, Repr

structure ContingentSale where
  baseSale : InstallmentSale
  contingentType : ContingentSaleType
  maximumPrice : Option Currency
  maximumPeriod : Option Nat  -- Years
  deriving Repr

-- Basis allocation for contingent sales
def annualBasisAllocation (sale : ContingentSale) : Currency :=
  match sale.contingentType with
  | .StatedMaximum =>
      -- Allocate basis proportionally to maximum price
      match sale.maximumPrice with
      | some _ =>
          let totalPaymentYears := sale.baseSale.subsequentPayments.length + 1
          if totalPaymentYears = 0 then 0
          else sale.baseSale.adjustedBasis / totalPaymentYears
      | none => 0
  | .FixedPeriod =>
      -- Allocate basis ratably over the period
      match sale.maximumPeriod with
      | some years => if years = 0 then 0 else sale.baseSale.adjustedBasis / years
      | none => 0
  | .Neither =>
      -- Basis recovery method - recover all basis first
      sale.baseSale.adjustedBasis

/-!
## Key Theorems - Loophole Detection
-/

-- Theorem: Gross profit ratio determines deferral benefit
theorem deferral_proportional_to_gain (sale : InstallmentSale)
    (h_qual : qualifiesForInstallmentMethod sale)
    (h_gain : grossProfit sale > 0) :
    -- Higher gross profit ratio = more tax deferred per payment
    grossProfitRatio sale > 0 := by
  unfold grossProfitRatio
  simp
  sorry -- Arithmetic with division

-- Theorem: Below $5M threshold avoids interest charge
theorem threshold_avoidance (sale : InstallmentSale) (afterYear : TaxYear)
    (taxRate interestRate : Rat)
    (h_under : sale.sellingPrice ≤ installmentThreshold) :
    interestOnDeferredTax sale afterYear taxRate interestRate = 0 := by
  unfold interestOnDeferredTax isLargeInstallmentSale installmentThreshold at *
  simp only [decide_eq_true_eq, not_lt.mpr h_under, ↓reduceIte]

-- Theorem: Related party 2-year rule creates holding requirement
theorem related_party_holding_loophole (sale : InstallmentSale) (resale : Resale)
    (h_related : sale.isRelatedPartySale = true)
    (h_held_2yr : yearsFromOriginalSale sale resale >= 2) :
    acceleratedGain sale resale = 0 := by
  unfold acceleratedGain triggersRelatedPartyRule
  simp [h_related, h_held_2yr, relatedPartyHoldingPeriod]

-- LOOPHOLE: Split sale into multiple transactions under $5M each
theorem splitting_avoids_interest (sale1 sale2 : InstallmentSale)
    (h_s1_under : sale1.sellingPrice ≤ installmentThreshold)
    (h_s2_under : sale2.sellingPrice ≤ installmentThreshold)
    (h_combined_over : sale1.sellingPrice + sale2.sellingPrice > installmentThreshold)
    (afterYear : TaxYear) (taxRate interestRate : Rat) :
    interestOnDeferredTax sale1 afterYear taxRate interestRate = 0 ∧
    interestOnDeferredTax sale2 afterYear taxRate interestRate = 0 := by
  constructor
  · exact threshold_avoidance sale1 afterYear taxRate interestRate h_s1_under
  · exact threshold_avoidance sale2 afterYear taxRate interestRate h_s2_under

-- Theorem: Contingent sales can defer basis recovery
theorem contingent_basis_timing (sale : ContingentSale)
    (h_neither : sale.contingentType = .Neither) :
    -- All basis recovered before recognizing gain
    annualBasisAllocation sale = sale.baseSale.adjustedBasis := by
  unfold annualBasisAllocation
  simp [h_neither]

/-!
## Loophole Scenarios
-/

def exampleYear2024 : TaxYear := ⟨2024, by omega⟩
def exampleYear2025 : TaxYear := ⟨2025, by omega⟩
def exampleYear2026 : TaxYear := ⟨2026, by omega⟩

-- Scenario: Standard installment sale
def standardInstallmentSale : InstallmentSale := {
  sellingPrice := 1000000
  adjustedBasis := 400000
  propertyType := .RealProperty
  saleYear := exampleYear2024
  yearOfSalePayment := 200000  -- 20% down
  subsequentPayments := [
    (exampleYear2025, 400000),
    (exampleYear2026, 400000)
  ]
  isRelatedPartySale := false
  buyerId := 1
  sellerId := 2
}

#eval qualifiesForInstallmentMethod standardInstallmentSale
#eval grossProfit standardInstallmentSale  -- 600000
#eval grossProfitRatio standardInstallmentSale  -- 0.6
#eval gainInYearOfSale standardInstallmentSale  -- 120000 (200000 × 0.6)
#eval totalGainRecognized standardInstallmentSale  -- Should equal grossProfit

-- Scenario: Large sale triggering interest charge
def largeSale : InstallmentSale := {
  sellingPrice := 10000000  -- $10M
  adjustedBasis := 2000000
  propertyType := .RealProperty
  saleYear := exampleYear2024
  yearOfSalePayment := 2000000
  subsequentPayments := [
    (exampleYear2025, 4000000),
    (exampleYear2026, 4000000)
  ]
  isRelatedPartySale := false
  buyerId := 1
  sellerId := 2
}

#eval isLargeInstallmentSale largeSale  -- true
#eval deferredGain largeSale exampleYear2024  -- Deferred after year 1

-- Scenario: Related party sale with early resale
def relatedPartySale : InstallmentSale := {
  sellingPrice := 500000
  adjustedBasis := 200000
  propertyType := .PersonalProperty
  saleYear := exampleYear2024
  yearOfSalePayment := 100000
  subsequentPayments := [(exampleYear2025, 200000), (exampleYear2026, 200000)]
  isRelatedPartySale := true  -- Key!
  buyerId := 1
  sellerId := 2
}

def earlyResale : Resale := {
  originalSale := relatedPartySale
  resaleDate := exampleYear2025  -- Only 1 year later!
  resaleProceeds := 600000
}

#eval triggersRelatedPartyRule relatedPartySale earlyResale  -- true
#eval acceleratedGain relatedPartySale earlyResale  -- Gain accelerated!

-- Scenario: Split sale to avoid $5M threshold
def splitSale1 : InstallmentSale := {
  sellingPrice := 4500000  -- Under $5M
  adjustedBasis := 1000000
  propertyType := .RealProperty
  saleYear := exampleYear2024
  yearOfSalePayment := 500000
  subsequentPayments := [(exampleYear2025, 2000000), (exampleYear2026, 2000000)]
  isRelatedPartySale := false
  buyerId := 1
  sellerId := 2
}

def splitSale2 : InstallmentSale := {
  sellingPrice := 4500000  -- Under $5M
  adjustedBasis := 1000000
  propertyType := .RealProperty
  saleYear := exampleYear2024
  yearOfSalePayment := 500000
  subsequentPayments := [(exampleYear2025, 2000000), (exampleYear2026, 2000000)]
  isRelatedPartySale := false
  buyerId := 3  -- Different buyer
  sellerId := 2
}

-- Combined = $9M, but each under $5M = no interest charge!
#eval isLargeInstallmentSale splitSale1  -- false
#eval isLargeInstallmentSale splitSale2  -- false

end
