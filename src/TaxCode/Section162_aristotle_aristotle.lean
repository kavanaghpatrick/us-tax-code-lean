/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4cf38843-09cd-4d38-ac02-71b9e6215b0e

The following was proved by Aristotle:

- theorem deductions_nonnegative (expenses : List BusinessExpense)
    (h : ∀ e ∈ expenses, (e.amount : Int) ≥ 0) :
    calculateSection162Deduction expenses ≥ 0
-/

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
# IRC Section 162 - Trade or Business Expenses

Allows deduction of all ordinary and necessary expenses paid or incurred during
the taxable year in carrying on any trade or business.

## References
- [26 USC §162](https://www.law.cornell.edu/uscode/text/26/162)

## Key Provisions
- Ordinary and necessary business expenses are deductible
- Includes: salaries, travel expenses, rentals
- Must be for carrying on trade or business
- Expenses must be reasonable and not lavish/extravagant
-/

-- Business expense types
inductive BusinessExpenseType
  | Salaries               -- §162(a)(1) - compensation for services
  | TravelMeals           -- §162(a)(2) - travel and meals (away from home)
  | Rentals               -- §162(a)(3) - property rentals
  | SuppliesInventory     -- Ordinary business supplies
  | Advertising           -- Advertising and marketing
  | Insurance             -- Business insurance premiums
  | Utilities             -- Business utilities
  | ProfessionalFees      -- Legal, accounting, consulting fees
  | Depreciation          -- Depreciation of business assets
  | Other (description : String)
  deriving Repr, DecidableEq

-- Business expense structure
structure BusinessExpense where
  amount : Currency
  expenseType : BusinessExpenseType
  isOrdinary : Bool        -- Is this an ordinary expense for the business?
  isNecessary : Bool       -- Is this necessary for the business?
  isReasonable : Bool      -- Is the amount reasonable?
  isForTradeBusiness : Bool -- Is it for carrying on trade or business?
  deriving Repr

-- Check if expense qualifies for §162 deduction
def qualifiesForDeduction (expense : BusinessExpense) : Bool :=
  expense.isOrdinary &&
  expense.isNecessary &&
  expense.isReasonable &&
  expense.isForTradeBusiness

-- Calculate total §162 deductions from a list of expenses
def calculateSection162Deduction (expenses : List BusinessExpense) : Currency :=
  expenses.foldl (fun (acc : Int) e =>
    let amt : Int := e.amount
    if qualifiesForDeduction e then acc + amt else acc) (0 : Int)

-- Helper: Create a qualifying business expense
def makeBusinessExpense (amount : Currency) (expenseType : BusinessExpenseType) : BusinessExpense :=
  ⟨amount, expenseType, true, true, true, true⟩

-- Examples
def example_salary_expense : BusinessExpense :=
  makeBusinessExpense 5000000 BusinessExpenseType.Salaries

-- $50,000 salary

def example_travel_expense : BusinessExpense :=
  makeBusinessExpense 150000 BusinessExpenseType.TravelMeals

-- $1,500 travel

def example_lavish_expense : BusinessExpense :=
  ⟨500000, BusinessExpenseType.TravelMeals, true, true, false, true⟩

-- $5,000 lavish meal (NOT reasonable)

def example_business : List BusinessExpense := [
  example_salary_expense,
  example_travel_expense,
  example_lavish_expense
]

#eval qualifiesForDeduction example_salary_expense

-- true
#eval qualifiesForDeduction example_travel_expense

-- true
#eval qualifiesForDeduction example_lavish_expense

-- false (not reasonable)
#eval calculateSection162Deduction example_business

-- 5150000 ($51,500)

-- Theorem: Only qualifying expenses are deducted
theorem only_qualifying_deducted (e : BusinessExpense)
    (h : ¬qualifiesForDeduction e) :
    calculateSection162Deduction [e] = 0 := by
  simp [calculateSection162Deduction, h]

-- Theorem: Deductions are non-negative
theorem deductions_nonnegative (expenses : List BusinessExpense)
    (h : ∀ e ∈ expenses, (e.amount : Int) ≥ 0) :
    calculateSection162Deduction expenses ≥ 0 := by
  -- By definition of `calculateSection162Deduction`, we know that it is the sum of non-negative amounts.
  have h_sum_nonneg : ∀ (expenses : List BusinessExpense), (∀ e ∈ expenses, e.amount ≥ 0) → calculateSection162Deduction expenses ≥ 0 := by
    aesop;
    induction expenses_1 using List.reverseRecOn <;> aesop;
    · decide +revert;
    · cases a_1 ; unfold calculateSection162Deduction at * ; aesop;
      exact le_trans a_2 ( Int.le_add_of_nonneg_right ( a _ ( Or.inr rfl ) ) );
  exact h_sum_nonneg expenses h

-- Theorem: All qualifying expenses with non-negative amounts contribute to deduction
theorem qualifying_expenses_count (e : BusinessExpense)
    (h1 : qualifiesForDeduction e)
    (h2 : (e.amount : Int) ≥ 0) :
    calculateSection162Deduction [e] = e.amount := by
  simp [calculateSection162Deduction, h1]