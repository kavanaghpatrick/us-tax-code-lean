import Common.Basic

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
  makeBusinessExpense 5000000 BusinessExpenseType.Salaries  -- $50,000 salary

def example_travel_expense : BusinessExpense :=
  makeBusinessExpense 150000 BusinessExpenseType.TravelMeals  -- $1,500 travel

def example_lavish_expense : BusinessExpense :=
  ⟨500000, BusinessExpenseType.TravelMeals, true, true, false, true⟩  -- $5,000 lavish meal (NOT reasonable)

def example_business : List BusinessExpense := [
  example_salary_expense,
  example_travel_expense,
  example_lavish_expense
]

#eval qualifiesForDeduction example_salary_expense    -- true
#eval qualifiesForDeduction example_travel_expense    -- true
#eval qualifiesForDeduction example_lavish_expense    -- false (not reasonable)
#eval calculateSection162Deduction example_business   -- 5150000 ($51,500)

-- Theorem: Only qualifying expenses are deducted
theorem only_qualifying_deducted (e : BusinessExpense)
    (h : ¬qualifiesForDeduction e) :
    calculateSection162Deduction [e] = 0 := by
  simp [calculateSection162Deduction, h]

-- Theorem: Deductions are non-negative
theorem deductions_nonnegative (expenses : List BusinessExpense)
    (h : ∀ e ∈ expenses, (e.amount : Int) ≥ 0) :
    calculateSection162Deduction expenses ≥ 0 := by
  sorry

-- Theorem: All qualifying expenses with non-negative amounts contribute to deduction
theorem qualifying_expenses_count (e : BusinessExpense)
    (h1 : qualifiesForDeduction e)
    (h2 : (e.amount : Int) ≥ 0) :
    calculateSection162Deduction [e] = e.amount := by
  simp [calculateSection162Deduction, h1]
