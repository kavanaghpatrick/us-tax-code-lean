/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1e9f0eb1-768b-4a39-bbe7-a309379848e6
-/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  HAdd Currency Currency ?m.8

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HAdd Currency ℤ ?m.8

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HAdd ℤ Currency ?m.8

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HSub Currency Currency ?m.8

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HSub Currency ℤ ?m.8

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HSub ℤ Currency ?m.8

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HMul Currency Currency ?m.8

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HMul Currency ℤ ?m.8

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HMul ℤ Currency ?m.8

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HDiv Currency ℤ ?m.8

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HDiv Currency Currency ?m.8

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Max Currency

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Min Currency

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Neg Currency

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
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

-- Arithmetic instances for Currency (since Currency := Int)
instance : HAdd Currency Currency Currency where
  hAdd a b := a + b

instance : HAdd Currency Int Currency where
  hAdd a b := a + b

instance : HAdd Int Currency Currency where
  hAdd a b := a + b

instance : HSub Currency Currency Currency where
  hSub a b := a - b

instance : HSub Currency Int Currency where
  hSub a b := a - b

instance : HSub Int Currency Currency where
  hSub a b := a - b

instance : HMul Currency Currency Currency where
  hMul a b := a * b

instance : HMul Currency Int Currency where
  hMul a b := a * b

instance : HMul Int Currency Currency where
  hMul a b := a * b

instance : HDiv Currency Int Currency where
  hDiv a b := a / b

instance : HDiv Currency Currency Currency where
  hDiv a b := a / b

instance : Max Currency where
  max a b := max a b

instance : Min Currency where
  min a b := min a b

instance : Neg Currency where
  neg a := -a

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
# IRC Section 64 - Ordinary Income Defined

For purposes of the Internal Revenue Code, defines "ordinary income" as including
any gain from the sale or exchange of property which is neither a capital asset
nor property described in IRC §1231(b).

## References
- [26 USC §64](https://www.law.cornell.edu/uscode/text/26/64)

## Key Provisions
- Ordinary income includes gains from non-capital, non-§1231(b) property
- Any gain treated as "ordinary income" under other IRC provisions is also ordinary income
-/

-- Property classification for income purposes
inductive PropertyType
  | CapitalAsset               -- IRC §1221 capital asset
  | Section1231Property        -- IRC §1231(b) property (trade/business property)
  | OrdinaryIncomeProperty     -- Neither capital nor §1231(b)
  deriving Repr, DecidableEq

-- Gain from sale or exchange
structure PropertyGain where
  amount : Currency
  propertyType : PropertyType
  deriving Repr

-- Determine if a gain is ordinary income
def isOrdinaryIncome (gain : PropertyGain) : Bool :=
  match gain.propertyType with
  | PropertyType.CapitalAsset => false          -- Capital gains, not ordinary
  | PropertyType.Section1231Property => false   -- §1231 treatment
  | PropertyType.OrdinaryIncomeProperty => true

-- Ordinary income

-- Calculate ordinary income from a list of gains
def calculateOrdinaryIncome (gains : List PropertyGain) : Currency :=
  gains.foldl (fun (acc : Int) g =>
    let amt : Int := g.amount
    if isOrdinaryIncome g then acc + amt else acc) (0 : Int)

-- Examples
def example_inventory_sale : PropertyGain :=
  ⟨50000, PropertyType.OrdinaryIncomeProperty⟩

-- $500 gain from inventory

def example_stock_sale : PropertyGain :=
  ⟨100000, PropertyType.CapitalAsset⟩

-- $1,000 gain from stock

#eval isOrdinaryIncome example_inventory_sale

-- true
#eval isOrdinaryIncome example_stock_sale

-- false
#eval calculateOrdinaryIncome [example_inventory_sale, example_stock_sale]

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Invalid field notation: Type is not of the form `C ...` where C is a constant
  g
has type
  PropertyGain
Function expected at
  calculateOrdinaryIncome
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  gains-/
-- 50000

-- Theorem: Ordinary income is non-negative
theorem ordinary_income_nonnegative (gains : List PropertyGain)
    (h : ∀ g ∈ gains, (g.amount : Int) ≥ 0) :
    calculateOrdinaryIncome gains ≥ 0 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Invalid field notation: Type is not of the form `C ...` where C is a constant
  g
has type
  PropertyGain
Unknown identifier `PropertyType.CapitalAsset`
Function expected at
  isOrdinaryIncome
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  g-/
-- Theorem: Capital asset gains don't contribute to ordinary income
theorem capital_gains_excluded (g : PropertyGain)
    (h : g.propertyType = PropertyType.CapitalAsset) :
    isOrdinaryIncome g = false := by
  simp [isOrdinaryIncome, h]