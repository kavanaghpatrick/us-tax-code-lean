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
  | PropertyType.OrdinaryIncomeProperty => true -- Ordinary income

-- Calculate ordinary income from a list of gains
def calculateOrdinaryIncome (gains : List PropertyGain) : Currency :=
  gains.foldl (fun (acc : Int) g =>
    let amt : Int := g.amount
    if isOrdinaryIncome g then acc + amt else acc) (0 : Int)

-- Examples
def example_inventory_sale : PropertyGain :=
  ⟨50000, PropertyType.OrdinaryIncomeProperty⟩  -- $500 gain from inventory

def example_stock_sale : PropertyGain :=
  ⟨100000, PropertyType.CapitalAsset⟩           -- $1,000 gain from stock

#eval isOrdinaryIncome example_inventory_sale   -- true
#eval isOrdinaryIncome example_stock_sale       -- false
#eval calculateOrdinaryIncome [example_inventory_sale, example_stock_sale]  -- 50000

-- Theorem: Ordinary income is non-negative
theorem ordinary_income_nonnegative (gains : List PropertyGain)
    (h : ∀ g ∈ gains, (g.amount : Int) ≥ 0) :
    calculateOrdinaryIncome gains ≥ 0 := by
  sorry

-- Theorem: Capital asset gains don't contribute to ordinary income
theorem capital_gains_excluded (g : PropertyGain)
    (h : g.propertyType = PropertyType.CapitalAsset) :
    isOrdinaryIncome g = false := by
  simp [isOrdinaryIncome, h]
