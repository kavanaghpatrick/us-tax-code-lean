import Common.Basic

/-!
# IRC Section 32 - Earned Income Credit (EITC)

The Earned Income Tax Credit is one of the most impactful anti-poverty provisions
in the US tax code, providing refundable credits to low-to-moderate income workers.

## References
- [26 USC §32](https://www.law.cornell.edu/uscode/text/26/32)
- [IRS EITC](https://www.irs.gov/credits-deductions/individuals/earned-income-tax-credit)

## Key Features (2024)
- Fully refundable credit
- Based on earned income and number of qualifying children
- Credit phases in, reaches max, then phases out
- Different schedules for 0, 1, 2, or 3+ children
- Maximum credits: ~$600 (0 kids), ~$3,995 (1 kid), ~$6,604 (2 kids), ~$7,430 (3+ kids)
-/

-- EITC eligibility and calculation structures

inductive EITCCategory
  | NoChildren
  | OneChild
  | TwoChildren  
  | ThreeOrMoreChildren
  deriving Repr, DecidableEq

namespace EITC2024

-- Maximum credit amounts by category (approximate 2024 values)
def maxCredit (category : EITCCategory) : Currency :=
  match category with
  | EITCCategory.NoChildren => 60000           -- ~$600
  | EITCCategory.OneChild => 399500            -- ~$3,995
  | EITCCategory.TwoChildren => 660400         -- ~$6,604
  | EITCCategory.ThreeOrMoreChildren => 743000 -- ~$7,430

-- Income at which max credit is reached (phase-in complete)
def phaseInComplete (category : EITCCategory) (mfj : Bool) : Currency :=
  match category with
  | EITCCategory.NoChildren => 780000          -- ~$7,800
  | EITCCategory.OneChild => 1175000           -- ~$11,750
  | EITCCategory.TwoChildren => 1650000        -- ~$16,500
  | EITCCategory.ThreeOrMoreChildren => 1650000

-- Income at which phase-out begins
def phaseOutBegin (category : EITCCategory) (mfj : Bool) : Currency :=
  let base : Int := match category with
    | EITCCategory.NoChildren => 990000         -- ~$9,900
    | EITCCategory.OneChild => 2062000          -- ~$20,620
    | EITCCategory.TwoChildren => 2062000
    | EITCCategory.ThreeOrMoreChildren => 2062000
  let boost : Int := 640000  -- MFJ gets ~$6,400 boost
  if mfj then base + boost else base

-- Income at which credit fully phases out (zero)
def phaseOutComplete (category : EITCCategory) (mfj : Bool) : Currency :=
  match category, mfj with
  | EITCCategory.NoChildren, false => 1810000      -- ~$18,100 single
  | EITCCategory.NoChildren, true => 2485000       -- ~$24,850 MFJ
  | EITCCategory.OneChild, false => 4821000        -- ~$48,210 single
  | EITCCategory.OneChild, true => 5549000         -- ~$55,490 MFJ
  | EITCCategory.TwoChildren, false => 5667000     -- ~$56,670 single
  | EITCCategory.TwoChildren, true => 6395000      -- ~$63,950 MFJ
  | EITCCategory.ThreeOrMoreChildren, false => 6350000  -- ~$63,500 single
  | EITCCategory.ThreeOrMoreChildren, true => 7078000   -- ~$70,780 MFJ

end EITC2024

-- Determine EITC category from number of qualifying children
def eitcCategory (qualifyingChildren : Nat) : EITCCategory :=
  if qualifyingChildren = 0 then EITCCategory.NoChildren
  else if qualifyingChildren = 1 then EITCCategory.OneChild
  else if qualifyingChildren = 2 then EITCCategory.TwoChildren
  else EITCCategory.ThreeOrMoreChildren

-- Calculate EITC
def calculateEITC (earnedIncome : Currency)
                  (agi : Currency)
                  (qualifyingChildren : Nat)
                  (filingStatus : FilingStatus) : Currency :=
  let category := eitcCategory qualifyingChildren
  let isMFJ := filingStatus = FilingStatus.MarriedFilingJointly
  let maxCredit : Int := EITC2024.maxCredit category
  let phaseInEnd : Int := EITC2024.phaseInComplete category isMFJ
  let phaseOutStart : Int := EITC2024.phaseOutBegin category isMFJ
  let phaseOutEnd : Int := EITC2024.phaseOutComplete category isMFJ

  -- Use lesser of earned income or AGI
  let earnedInt : Int := earnedIncome
  let agiInt : Int := agi
  let income : Int := if earnedInt < agiInt then earnedInt else agiInt

  if income ≥ phaseOutEnd then
    (0 : Int)  -- Fully phased out
  else if income ≤ phaseInEnd then
    -- Phase-in region: credit increases with income
    (income * maxCredit) / phaseInEnd
  else if income < phaseOutStart then
    -- Plateau: full credit
    maxCredit
  else
    -- Phase-out region: credit decreases
    let excessIncome : Int := income - phaseOutStart
    let phaseOutRange : Int := phaseOutEnd - phaseOutStart
    let reduction : Int := (excessIncome * maxCredit) / phaseOutRange
    let result : Int := maxCredit - reduction
    if result > 0 then result else (0 : Int)

-- Examples
def example_single_1_child_30k : Currency :=
  calculateEITC 3000000 3000000 1 FilingStatus.Single

#eval example_single_1_child_30k  -- Should be near max ~$3,995

def example_single_2_children_25k : Currency :=
  calculateEITC 2500000 2500000 2 FilingStatus.Single

#eval example_single_2_children_25k  -- Should be near max ~$6,604

-- Theorem: EITC is capped at maximum for category
theorem eitc_capped (earned : Currency) (agi : Currency) (children : Nat) (status : FilingStatus) :
    calculateEITC earned agi children status ≤ EITC2024.maxCredit (eitcCategory children) := by
  sorry

-- Theorem: EITC is zero above phase-out threshold
theorem eitc_phases_out (earned : Currency) (agi : Currency) (children : Nat) (status : FilingStatus)
    (earnedInt : Int := earned) (agiInt : Int := agi)
    (h : (if earnedInt < agiInt then earnedInt else agiInt) ≥
         EITC2024.phaseOutComplete (eitcCategory children)
         (status = FilingStatus.MarriedFilingJointly)) :
    calculateEITC earned agi children status = 0 := by
  sorry
