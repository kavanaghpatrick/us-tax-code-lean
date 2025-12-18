/-
IRC §1031 - Exchange of Real Property Held for Productive Use or Investment
Like-kind exchanges: No gain or loss recognized on exchange of real property held for
productive use or investment if exchanged solely for property of like-kind.
-/

import Lean

namespace Common.Basic

def Currency := Int

-- Currency instances for arithmetic operations
instance : Add Currency := inferInstanceAs (Add Int)
instance : Sub Currency := inferInstanceAs (Sub Int)
instance : Mul Currency := inferInstanceAs (Mul Int)
instance : Div Currency := inferInstanceAs (Div Int)
instance : LE Currency := inferInstanceAs (LE Int)
instance : LT Currency := inferInstanceAs (LT Int)
instance : DecidableRel ((· ≤ ·) : Currency → Currency → Prop) := inferInstanceAs (DecidableRel (· ≤ · : Int → Int → Prop))
instance : DecidableRel ((· < ·) : Currency → Currency → Prop) := inferInstanceAs (DecidableRel (· < · : Int → Int → Prop))
instance (n : Nat) [OfNat Int n] : OfNat Currency n := inferInstanceAs (OfNat Int n)
instance : Min Currency := inferInstanceAs (Min Int)

abbrev TaxYear := Nat

inductive FilingStatus where
  | Single                         -- IRC §1(c)
  | MarriedFilingJointly          -- IRC §1(a)
  | MarriedFilingSeparately       -- IRC §1(d)
  | HeadOfHousehold               -- IRC §1(b)
  | QualifyingWidower             -- IRC §2(b)
  | Estate                         -- IRC §1(e)(1)
  | Trust                          -- IRC §1(e)(2)
  deriving Repr, DecidableEq, Inhabited

end Common.Basic

structure Property where
  basis : Common.Basic.Currency
  fmv : Common.Basic.Currency

structure PropertyExchange where
  tax_year : Common.Basic.TaxYear
  filing_status : Common.Basic.FilingStatus
  given : Property
  received : Property
  boot_paid : Common.Basic.Currency
  boot_received : Common.Basic.Currency

def calculateGainRealized (ex : PropertyExchange) : Common.Basic.Currency :=
  ex.received.fmv + ex.boot_received - ex.given.basis

def calculateGainRecognized (ex : PropertyExchange) : Common.Basic.Currency :=
  let realized := calculateGainRealized ex
  if realized > 0 then
    min realized ex.boot_received
  else
    0

def calculateNewBasis (ex : PropertyExchange) : Common.Basic.Currency :=
  ex.given.basis + ex.boot_paid - ex.boot_received + calculateGainRecognized ex