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
# IRC Section 1011 - Adjusted basis for determining gain or loss

This file formalizes IRC §1011 (Adjusted basis for determining gain or loss).

## References
- [26 USC §1011](https://www.law.cornell.edu/uscode/text/26/1011)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1011 - Adjusted basis for determining gain or loss
   U.S. Code
   Notes
   prev |
   next
   (a)
   General rule
   The adjusted basis for determining the gain or loss from the sale or other
   disposition
   of property, whenever acquired, shall be the basis (determined under section 1012 or other applicable sections of this subchapter and subchapters C (relating to corporate distributions and adjustments), K (relating to partners and partnerships), and P (relating to capital gains and losses)), adjusted as provided in section 1016.
   (b)
   Bargain sale to a charitable organization
   If a deduction is allowable under section 170 (relating to charitable contributions) by reason of a sale, then the adjusted basis for determining the gain from such sale shall be that portion of the adjusted basis which bears the same ratio to the adjusted basis as the amount realized bears to the fair market value of the property.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 296
   ;
   Pub. L. 91–172, title II, § 201(f)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 564
   .)
   Editorial Notes
   Amendments
   1969—
   Pub. L. 91–172
   redesignated existing provisions as subsec. (a) and added subsec. (b).
   Statutory Notes and Related Subsidiaries
   Effective Date of 1969 Amendment
   Amendment by
   Pub. L. 91–172
   applicable with respect to sales made after
   Dec. 19, 1969
   , see
   section 201(g)(6) of Pub. L. 91–172
   , set out as a note under
   section 170 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/

-- TODO: Add type definitions

-- TODO: Add main functions

-- TODO: Add theorems to prove

-- Example usage
#eval "Section loaded"
