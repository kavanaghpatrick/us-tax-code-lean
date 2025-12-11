import Common.Basic

/-!
# IRC Section 1 - Tax Imposed

This file formalizes the tax rate schedules from 26 U.S. Code § 1.

## References
- [IRC §1](https://www.law.cornell.edu/uscode/text/26/1)
-/

-- Tax bracket definition
structure TaxBracket where
  lowerBound : Currency      -- Inclusive lower bound (in cents)
  upperBound : Option Currency  -- Exclusive upper bound (None = infinity)
  rateNumerator : Nat        -- Tax rate numerator (e.g., 10 for 10%)
  rateDenominator : Nat      -- Tax rate denominator (usually 100)
  h_denom_pos : rateDenominator > 0
  deriving Repr

namespace TaxBracket

-- Calculate tax for income within this bracket
def taxInBracket (bracket : TaxBracket) (income : Currency) : Currency :=
  let inc : Int := income
  let lower : Int := bracket.lowerBound
  let incomeInBracket : Int := match bracket.upperBound with
    | none => max 0 (inc - lower)
    | some upper =>
      let upp : Int := upper
      max 0 (min (upp - lower) (inc - lower))
  (incomeInBracket * (bracket.rateNumerator : Int)) / (bracket.rateDenominator : Int)

end TaxBracket

-- Tax rate schedule for a specific filing status and year
structure RateSchedule where
  filingStatus : FilingStatus
  taxYear : TaxYear
  brackets : List TaxBracket
  h_nonempty : brackets ≠ []
  -- TODO: Add proof that brackets are contiguous and ordered

-- Calculate total tax using a rate schedule
def calculateTaxFromSchedule (schedule : RateSchedule) (income : Currency) : Currency :=
  schedule.brackets.foldl (fun (acc : Int) bracket =>
    let tax : Int := bracket.taxInBracket income
    acc + tax) (0 : Int)

-- 2024 Single Filer Rate Schedule (IRC §1(c))
-- Note: These are example values and should be updated annually per IRC §1(f)
def singleFiler2024Brackets : List TaxBracket := sorry
  -- TODO: Define actual 2024 brackets
  -- This will be filled by Aristotle based on the documentation

def singleFiler2024Schedule : RateSchedule := sorry
  -- TODO: Construct complete rate schedule
  -- This will be filled by Aristotle

-- Main tax calculation function
def calculateIncomeTax (income : Currency) (status : FilingStatus) (year : TaxYear) : Currency :=
  sorry  -- TODO: Implement lookup of correct rate schedule and calculation

-- Properties to prove
theorem tax_monotonic (income1 income2 : Currency) (status : FilingStatus) (year : TaxYear) :
    (income1 : Int) ≤ (income2 : Int) →
    (calculateIncomeTax income1 status year : Int) ≤ (calculateIncomeTax income2 status year : Int) := by
  sorry

theorem tax_nonnegative (income : Currency) (status : FilingStatus) (year : TaxYear) :
    (0 : Int) ≤ (income : Int) →
    (0 : Int) ≤ (calculateIncomeTax income status year : Int) := by
  sorry
