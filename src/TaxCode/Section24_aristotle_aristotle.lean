/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: aa9e7d34-df88-4a2f-84ee-c53de6a62554
-/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  HMul ℤ Currency ?m.9

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HSub Currency ℤ ?m.9

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HDiv Currency ℤ ?m.19

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HSub Currency Currency ?m.9

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Max Currency

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.
aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.-/
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
# IRC Section 24 - Child Tax Credit

Formalizes the child tax credit per 26 USC §24.

One of the most impactful provisions in the tax code, providing up to $2,000 per
qualifying child under age 17, with up to $1,700 refundable.

## References
- [26 USC §24](https://www.law.cornell.edu/uscode/text/26/24)
- [IRS Child Tax Credit](https://www.irs.gov/credits-deductions/individuals/child-tax-credit)

## Key Provisions (2024)
- $2,000 credit per qualifying child
- Up to $1,700 refundable (Additional Child Tax Credit)
- Child must be under 17 at end of tax year
- Income phase-out: $200k (single), $400k (MFJ)
- Phase-out rate: $50 per $1,000 over threshold
-/

-- Qualifying child for CTC purposes
structure QualifyingChild where
  age : Nat
  relationshipTest : Bool
  residencyTest : Bool
  supportTest : Bool
  citizenshipTest : Bool
  ssnRequired : Bool
  deriving Repr

namespace QualifyingChild

def qualifiesForCTC (child : QualifyingChild) (taxYear : TaxYear) : Bool :=
  child.age < 17 &&
  child.relationshipTest &&
  child.residencyTest &&
  child.supportTest &&
  child.citizenshipTest &&
  child.ssnRequired

end QualifyingChild

namespace CTC2024

def creditPerChild : Currency := 200000

def refundableLimit : Currency := 170000

def phaseOutSingle : Currency := 20000000

def phaseOutMFJ : Currency := 40000000

def phaseOutRate : Nat := 50

end CTC2024

def calculateBaseCTC (qualifyingChildren : List QualifyingChild) (taxYear : TaxYear) : Currency :=
  let count := qualifyingChildren.filter (fun c => c.qualifiesForCTC taxYear) |>.length
  (count : Int) * CTC2024.creditPerChild

def calculateCTCPhaseOut (modifiedAGI : Currency) (filingStatus : FilingStatus) : Currency :=
  let threshold := match filingStatus with
    | FilingStatus.Single => CTC2024.phaseOutSingle
    | FilingStatus.MarriedFilingJointly => CTC2024.phaseOutMFJ
    | FilingStatus.MarriedFilingSeparately => CTC2024.phaseOutMFJ / 2
    | FilingStatus.HeadOfHousehold => CTC2024.phaseOutSingle
    | FilingStatus.QualifyingWidower => CTC2024.phaseOutMFJ
  let excessIncome : Int := max 0 (modifiedAGI - threshold)
  let excessThousands : Int := (excessIncome + 99900) / 100000
  excessThousands * (CTC2024.phaseOutRate : Int) * 100

def calculateCTC (qualifyingChildren : List QualifyingChild)
                 (modifiedAGI : Currency)
                 (filingStatus : FilingStatus)
                 (taxYear : TaxYear) : Currency :=
  let baseCTC := calculateBaseCTC qualifyingChildren taxYear
  let phaseOut := calculateCTCPhaseOut modifiedAGI filingStatus
  max 0 (baseCTC - phaseOut)

def example_family_2_kids : List QualifyingChild := [
  ⟨5, true, true, true, true, true⟩,
  ⟨8, true, true, true, true, true⟩
]

#eval calculateBaseCTC example_family_2_kids ⟨2024, by decide⟩

#eval calculateCTC example_family_2_kids 45000000 FilingStatus.MarriedFilingJointly ⟨2024, by decide⟩