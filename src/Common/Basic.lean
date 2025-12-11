/-
Common definitions for US Tax Code formalization
-/

-- Currency represented in cents (to avoid floating point issues)
-- Example: $100.50 = 10050 cents
def Currency := Int
  deriving Repr, DecidableEq

namespace Currency

-- Constructor from dollars and cents
def make (dollars : Int) (cents : Nat) : Currency :=
  dollars * 100 + (cents : Int)

-- Zero currency
def zero : Currency := (0 : Int)

-- Convert cents to dollars (with truncation)
def toDollars (c : Currency) : Int :=
  let ci : Int := c
  ci / 100

instance : OfNat Currency n := ⟨(n : Int)⟩

-- Since Currency is Int, we can use Int's ordering
instance : LE Currency where
  le a b := @LE.le Int _ a b

instance : LT Currency where
  lt a b := @LT.lt Int _ a b

end Currency

-- Tax Year
structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913  -- First year of modern income tax (16th Amendment)

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

-- Filing Status (IRC §1(a)-(d) and §2(b))
inductive FilingStatus
  | Single                         -- IRC §1(c)
  | MarriedFilingJointly          -- IRC §1(a)
  | MarriedFilingSeparately       -- IRC §1(d)
  | HeadOfHousehold               -- IRC §1(b)
  | QualifyingWidower             -- IRC §2(b)
  deriving Repr, DecidableEq, Inhabited

-- Taxpayer entity
structure Taxpayer where
  id : String  -- SSN or EIN
  filingStatus : FilingStatus
  taxYear : TaxYear

instance : Repr Taxpayer where
  reprPrec t _ := s!"Taxpayer(id: {t.id}, status: {repr t.filingStatus}, year: {t.taxYear.year})"
