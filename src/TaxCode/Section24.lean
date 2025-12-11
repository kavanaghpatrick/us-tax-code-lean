import Common.Basic

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
