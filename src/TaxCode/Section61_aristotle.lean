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

-- Arithmetic instances for Currency (delegates to Int since Currency := Int)
instance : HAdd Currency Currency Currency where
  hAdd a b := Int.add a b

instance : HAdd Currency Int Currency where
  hAdd a b := Int.add a b

instance : HAdd Int Currency Currency where
  hAdd a b := Int.add a b

instance : HSub Currency Currency Currency where
  hSub a b := Int.sub a b

instance : HSub Currency Int Currency where
  hSub a b := Int.sub a b

instance : HSub Int Currency Currency where
  hSub a b := Int.sub a b

instance : HMul Currency Currency Currency where
  hMul a b := Int.mul a b

instance : HMul Currency Int Currency where
  hMul a b := Int.mul a b

instance : HMul Int Currency Currency where
  hMul a b := Int.mul a b

instance : HDiv Currency Int Currency where
  hDiv a b := Int.tdiv a b

instance : HDiv Currency Currency Currency where
  hDiv a b := Int.tdiv a b

instance : Max Currency where
  max a b := let ai : Int := a; let bi : Int := b; if ai ≤ bi then bi else ai

instance : Min Currency where
  min a b := let ai : Int := a; let bi : Int := b; if ai ≤ bi then ai else bi

instance : Neg Currency where
  neg a := Int.neg a

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
