/-
Common definitions inlined for Aristotle processing
-/

-- Currency represented in cents (to avoid floating point issues)
def Currency := Int
  deriving Repr, DecidableEq

namespace Currency

def make (dollars : Int) (cents : Nat) : Currency :=
  dollars * 100 + (cents : Int)

def zero : Currency := (0 : Int)

def toDollars (c : Currency) : Int :=
  let ci : Int := c
  ci / 100

instance : OfNat Currency n := ⟨(n : Int)⟩

instance : LE Currency where
  le a b := @LE.le Int _ a b

instance : LT Currency where
  lt a b := @LT.lt Int _ a b

end Currency

-- Tax Year
structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913

namespace TaxYear

def current : TaxYear := ⟨2024, by decide⟩

instance : DecidableEq TaxYear := fun a b =>
  match a, b with
  | ⟨y1, _⟩, ⟨y2, _⟩ =>
    if h : y1 = y2 then
      isTrue (by cases h; rfl)
    else
      isFalse (by intro eq; cases eq; exact h rfl)

end TaxYear

-- Filing Status
inductive FilingStatus
  | Single
  | MarriedFilingJointly
  | MarriedFilingSeparately
  | HeadOfHousehold
  | QualifyingWidower
  deriving Repr, DecidableEq, Inhabited

structure Taxpayer where
  id : String
  filingStatus : FilingStatus
  taxYear : TaxYear

instance : Repr Taxpayer where
  reprPrec t _ := s!"Taxpayer(id: {t.id}, status: {repr t.filingStatus}, year: {t.taxYear.year})"


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
-- Source: IRS 2024 Tax Brackets
def singleFiler2024Brackets : List TaxBracket := [
  ⟨0,        some 1160000,  10, 100, by decide⟩,  -- 10% on $0 - $11,600
  ⟨1160000,  some 4715000,  12, 100, by decide⟩,  -- 12% on $11,600 - $47,150
  ⟨4715000,  some 10052500, 22, 100, by decide⟩,  -- 22% on $47,150 - $100,525
  ⟨10052500, some 19195000, 24, 100, by decide⟩,  -- 24% on $100,525 - $191,950
  ⟨19195000, some 24372500, 32, 100, by decide⟩,  -- 32% on $191,950 - $243,725
  ⟨24372500, some 60935000, 35, 100, by decide⟩,  -- 35% on $243,725 - $609,350
  ⟨60935000, none,          37, 100, by decide⟩   -- 37% on $609,350+
]

def singleFiler2024Schedule : RateSchedule :=
  ⟨FilingStatus.Single, ⟨2024, by decide⟩, singleFiler2024Brackets, by simp [singleFiler2024Brackets]⟩

-- 2024 Married Filing Jointly Rate Schedule (IRC §1(a))
def marriedFilingJointly2024Brackets : List TaxBracket := [
  ⟨0,        some 2320000,  10, 100, by decide⟩,  -- 10% on $0 - $23,200
  ⟨2320000,  some 9430000,  12, 100, by decide⟩,  -- 12% on $23,200 - $94,300
  ⟨9430000,  some 20105000, 22, 100, by decide⟩,  -- 22% on $94,300 - $201,050
  ⟨20105000, some 38390000, 24, 100, by decide⟩,  -- 24% on $201,050 - $383,900
  ⟨38390000, some 48745000, 32, 100, by decide⟩,  -- 32% on $383,900 - $487,450
  ⟨48745000, some 73120000, 35, 100, by decide⟩,  -- 35% on $487,450 - $731,200
  ⟨73120000, none,          37, 100, by decide⟩   -- 37% on $731,200+
]

def marriedFilingJointly2024Schedule : RateSchedule :=
  ⟨FilingStatus.MarriedFilingJointly, ⟨2024, by decide⟩, marriedFilingJointly2024Brackets, by simp [marriedFilingJointly2024Brackets]⟩

-- 2024 Married Filing Separately Rate Schedule (IRC §1(d))
def marriedFilingSeparately2024Brackets : List TaxBracket := [
  ⟨0,        some 1160000,  10, 100, by decide⟩,  -- 10% on $0 - $11,600
  ⟨1160000,  some 4715000,  12, 100, by decide⟩,  -- 12% on $11,600 - $47,150
  ⟨4715000,  some 10052500, 22, 100, by decide⟩,  -- 22% on $47,150 - $100,525
  ⟨10052500, some 19195000, 24, 100, by decide⟩,  -- 24% on $100,525 - $191,950
  ⟨19195000, some 24372500, 32, 100, by decide⟩,  -- 32% on $191,950 - $243,725
  ⟨24372500, some 36560000, 35, 100, by decide⟩,  -- 35% on $243,725 - $365,600
  ⟨36560000, none,          37, 100, by decide⟩   -- 37% on $365,600+
]

def marriedFilingSeparately2024Schedule : RateSchedule :=
  ⟨FilingStatus.MarriedFilingSeparately, ⟨2024, by decide⟩, marriedFilingSeparately2024Brackets, by simp [marriedFilingSeparately2024Brackets]⟩

-- 2024 Head of Household Rate Schedule (IRC §1(b))
def headOfHousehold2024Brackets : List TaxBracket := [
  ⟨0,        some 1655000,  10, 100, by decide⟩,  -- 10% on $0 - $16,550
  ⟨1655000,  some 6310000,  12, 100, by decide⟩,  -- 12% on $16,550 - $63,100
  ⟨6310000,  some 10050000, 22, 100, by decide⟩,  -- 22% on $63,100 - $100,500
  ⟨10050000, some 19195000, 24, 100, by decide⟩,  -- 24% on $100,500 - $191,950
  ⟨19195000, some 24370000, 32, 100, by decide⟩,  -- 32% on $191,950 - $243,700
  ⟨24370000, some 60935000, 35, 100, by decide⟩,  -- 35% on $243,700 - $609,350
  ⟨60935000, none,          37, 100, by decide⟩   -- 37% on $609,350+
]

def headOfHousehold2024Schedule : RateSchedule :=
  ⟨FilingStatus.HeadOfHousehold, ⟨2024, by decide⟩, headOfHousehold2024Brackets, by simp [headOfHousehold2024Brackets]⟩

-- Qualifying Widow(er) uses same schedule as Married Filing Jointly (IRC §2(b))
def qualifyingWidower2024Schedule : RateSchedule :=
  ⟨FilingStatus.QualifyingWidower, ⟨2024, by decide⟩, marriedFilingJointly2024Brackets, by simp [marriedFilingJointly2024Brackets]⟩

-- Main tax calculation function
def calculateIncomeTax (income : Currency) (status : FilingStatus) (year : TaxYear) : Currency :=
  if year.year = 2024 then
    let schedule := match status with
      | FilingStatus.Single => singleFiler2024Schedule
      | FilingStatus.MarriedFilingJointly => marriedFilingJointly2024Schedule
      | FilingStatus.MarriedFilingSeparately => marriedFilingSeparately2024Schedule
      | FilingStatus.HeadOfHousehold => headOfHousehold2024Schedule
      | FilingStatus.QualifyingWidower => qualifyingWidower2024Schedule
    calculateTaxFromSchedule schedule income
  else
    0  -- TODO: Add schedules for other years

-- Properties to prove
theorem tax_monotonic (income1 income2 : Currency) (status : FilingStatus) (year : TaxYear) :
    (income1 : Int) ≤ (income2 : Int) →
    (calculateIncomeTax income1 status year : Int) ≤ (calculateIncomeTax income2 status year : Int) := by
  sorry

theorem tax_nonnegative (income : Currency) (status : FilingStatus) (year : TaxYear) :
    (0 : Int) ≤ (income : Int) →
    (0 : Int) ≤ (calculateIncomeTax income status year : Int) := by
  sorry
