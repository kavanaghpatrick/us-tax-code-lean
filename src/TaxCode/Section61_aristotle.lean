/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b1de0d2a-fe60-488d-ba10-6645118c2b83

Aristotle encountered an error while processing imports for this file.
Error:
unknown module prefix 'Common'

No directory 'Common' or file 'Common.olean' in the search path entries:
/code/harmonic-lean/.lake/packages/batteries/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/Qq/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/aesop/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/proofwidgets/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/importGraph/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/plausible/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/MD4Lean/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/BibtexQuery/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/UnicodeBasic/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/Cli/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/mathlib/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/doc-gen4/.lake/build/lib/lean
/code/harmonic-lean/.lake/build/lib/lean
/root/.elan/toolchains/leanprover--lean4---v4.24.0/lib/lean
/root/.elan/toolchains/leanprover--lean4---v4.24.0/lib/lean

-/

import Common.Basic

/-!
# IRC Section 61 - Gross Income Defined

Formalizes the definition of gross income per 26 USC §61.

"Except as otherwise provided in this subtitle, gross income means all income
from whatever source derived"

## References
- [26 USC §61](https://www.law.cornell.edu/uscode/text/26/61)

## Key Principle
Gross income is INCLUSIVE - it captures ALL income unless specifically excluded
by another IRC section (see Part III, §§101+).
-/

-- IRC §61(a) - Enumerated income sources (non-exhaustive list)
inductive IncomeSource
  | Compensation                    -- §61(a)(1): wages, fees, commissions, fringe benefits
  | BusinessIncome                  -- §61(a)(2): gross income from business
  | PropertyGains                   -- §61(a)(3): gains from dealings in property
  | Interest                        -- §61(a)(4): interest income
  | Rents                          -- §61(a)(5): rental income
  | Royalties                      -- §61(a)(6): royalty income
  | Dividends                      -- §61(a)(7): dividend income
  | Annuities                      -- §61(a)(8): annuity income
  | LifeInsurance                  -- §61(a)(9): income from life insurance/endowment contracts
  | Pensions                       -- §61(a)(10): pension income
  | DischargeOfIndebtedness        -- §61(a)(11): income from discharge of indebtedness
  | PartnershipDistribution        -- §61(a)(12): distributive share of partnership income
  | IncomeInRespectOfDecedent      -- §61(a)(13): income in respect of a decedent
  | EstateTrustIncome              -- §61(a)(14): income from estate or trust
  | Other (description : String)    -- Catch-all: "all income from whatever source derived"
  deriving Repr, DecidableEq

-- Income item with amount
structure IncomeItem where
  source : IncomeSource
  amount : Currency
  description : String
  deriving Repr

namespace IncomeItem

-- Create income items
def wages (amount : Currency) : IncomeItem :=
  ⟨IncomeSource.Compensation, amount, "Wages, salaries, tips"⟩

def interest (amount : Currency) : IncomeItem :=
  ⟨IncomeSource.Interest, amount, "Interest income"⟩

def dividends (amount : Currency) : IncomeItem :=
  ⟨IncomeSource.Dividends, amount, "Dividend income"⟩

def businessIncome (amount : Currency) : IncomeItem :=
  ⟨IncomeSource.BusinessIncome, amount, "Business income (Schedule C)"⟩

def capitalGains (amount : Currency) : IncomeItem :=
  ⟨IncomeSource.PropertyGains, amount, "Capital gains"⟩

end IncomeItem

-- Calculate total gross income from list of income items (IRC §61 general rule)
def calculateGrossIncome (incomeItems : List IncomeItem) : Currency :=
  incomeItems.foldl (fun (acc : Int) item =>
    let amt : Int := item.amount
    acc + amt) (0 : Int)

-- Theorem: Gross income is sum of all income items
theorem grossIncome_is_sum (items : List IncomeItem) :
    calculateGrossIncome items = items.foldl (fun (acc : Int) item => acc + (item.amount : Int)) (0 : Int) := by
  rfl

-- Theorem: Gross income is non-negative for non-negative inputs
theorem grossIncome_nonnegative (items : List IncomeItem)
    (h : ∀ item ∈ items, (0 : Int) ≤ (item.amount : Int)) :
    (0 : Int) ≤ (calculateGrossIncome items : Int) := by
  sorry

-- Theorem: Adding more income increases gross income (monotonicity)
theorem grossIncome_monotonic (items : List IncomeItem) (newItem : IncomeItem)
    (h : (0 : Int) ≤ (newItem.amount : Int)) :
    (calculateGrossIncome items : Int) ≤ (calculateGrossIncome (newItem :: items) : Int) := by
  sorry

-- Example: W-2 employee with wages and interest
def example_w2_employee : List IncomeItem := [
  IncomeItem.wages 5000000,        -- $50,000 wages
  IncomeItem.interest 50000,       -- $500 interest
  IncomeItem.dividends 25000       -- $250 dividends
]

#eval calculateGrossIncome example_w2_employee  -- Should be 5075000 ($50,750)
