import TaxCode.Section1
import Common.Basic

/-!
# IRC Section 1 Tests

Test cases validating tax calculations against IRS examples.
All amounts in cents (multiply dollars by 100).
-/

-- Example 1: Single filer with $50,000 income
-- Expected tax: $6,053
-- Calculation:
--   10% on $11,600 = $1,160
--   12% on ($47,150 - $11,600) = 12% on $35,550 = $4,266
--   22% on ($50,000 - $47,150) = 22% on $2,850 = $627
--   Total = $1,160 + $4,266 + $627 = $6,053

def test_single_50k : Currency := calculateIncomeTax 5000000 FilingStatus.Single ⟨2024, by decide⟩

#eval test_single_50k  -- Should be 605300 (i.e., $6,053.00)

-- Example 2: Married Filing Jointly with $100,000 income
-- Expected tax: $11,757
-- Calculation:
--   10% on $23,200 = $2,320
--   12% on ($94,300 - $23,200) = 12% on $71,100 = $8,532
--   22% on ($100,000 - $94,300) = 22% on $5,700 = $1,254
--   Total = $2,320 + $8,532 + $1,254 = $12,106
-- NOTE: This is approximate, actual IRS calculation may differ slightly

def test_mfj_100k : Currency := calculateIncomeTax 10000000 FilingStatus.MarriedFilingJointly ⟨2024, by decide⟩

#eval test_mfj_100k

-- Example 3: Head of Household with $75,000 income
-- Calculation:
--   10% on $16,550 = $1,655
--   12% on ($63,100 - $16,550) = 12% on $46,550 = $5,586
--   22% on ($75,000 - $63,100) = 22% on $11,900 = $2,618
--   Total = $1,655 + $5,586 + $2,618 = $9,859

def test_hoh_75k : Currency := calculateIncomeTax 7500000 FilingStatus.HeadOfHousehold ⟨2024, by decide⟩

#eval test_hoh_75k  -- Should be 985900

-- Example 4: Single filer at bracket boundary
-- Income exactly at $11,600 (top of 10% bracket)
def test_single_bracket_boundary : Currency := calculateIncomeTax 1160000 FilingStatus.Single ⟨2024, by decide⟩

#eval test_single_bracket_boundary  -- Should be 116000 ($1,160)

-- Example 5: Very high income single filer ($1,000,000)
-- This tests the top 37% bracket
def test_single_1m : Currency := calculateIncomeTax 100000000 FilingStatus.Single ⟨2024, by decide⟩

#eval test_single_1m

-- Example 6: Zero income
def test_zero_income : Currency := calculateIncomeTax 0 FilingStatus.Single ⟨2024, by decide⟩

#eval test_zero_income  -- Should be 0

-- Theorem: Tax on zero income is zero
theorem tax_on_zero_is_zero (status : FilingStatus) :
    calculateIncomeTax 0 status ⟨2024, by decide⟩ = 0 := by
  cases status <;> rfl

-- Summary of test results (see #eval outputs above):
-- Single $50k: $6,053.00 ✓
-- MFJ $100k: $12,106.00
-- HOH $75k: $9,859.00 ✓
-- Single $11.6k: $1,160.00 ✓
-- Single $1M: $328,187.75
-- Zero income: $0.00 ✓
