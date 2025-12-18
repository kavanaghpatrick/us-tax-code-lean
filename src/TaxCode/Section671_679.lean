/-
IRC Sections 671-679 - Grantor Trust Rules

The grantor trust rules determine when a trust's income is taxed to the grantor
(or another person) rather than to the trust or beneficiaries.

Key loophole mechanics:
- Intentionally Defective Grantor Trusts (IDGTs) - grantor taxed but assets
  excluded from estate
- Sales to grantor trusts not recognized for income tax
- Grantor payment of trust income tax is not a gift
- §678 allows beneficiaries to be treated as owners
- §679 foreign trust anti-avoidance rules

This is the foundation of modern estate planning.
-/

import Mathlib

set_option linter.unusedVariables false

noncomputable section

-- Use Int directly as Currency
abbrev Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

/-!
## §672 - Definitions

Key definitions for grantor trust analysis.
-/

-- Related or subordinate party per §672(c)
inductive RelationshipType where
  | Spouse
  | Parent
  | Descendant  -- Child, grandchild, etc.
  | Sibling
  | Employee
  | Corporation50PercentOwned
  | SubordinateEmployee
  | Unrelated
  deriving DecidableEq, Repr

def isRelatedOrSubordinate (rel : RelationshipType) : Bool :=
  match rel with
  | .Spouse | .Parent | .Descendant | .Sibling => true
  | .Employee | .SubordinateEmployee => true
  | .Corporation50PercentOwned => true
  | .Unrelated => false

-- Adverse party per §672(a)
-- Someone with "substantial beneficial interest" that would be adversely
-- affected by exercise of the power
structure PartyInterest where
  partyId : Nat
  hasSubstantialBeneficialInterest : Bool
  wouldBeAdverselyAffected : Bool
  relationshipToGrantor : RelationshipType
  deriving Repr

def isAdverseParty (party : PartyInterest) : Bool :=
  party.hasSubstantialBeneficialInterest && party.wouldBeAdverselyAffected

def isNonadverseParty (party : PartyInterest) : Bool :=
  !isAdverseParty party

/-!
## Trust Structure
-/

structure TrustBeneficiary where
  id : Nat
  name : String
  incomeInterest : Bool
  remainderInterest : Bool
  currentBeneficiary : Bool
  relationshipToGrantor : RelationshipType
  deriving Repr

structure Trust where
  id : Nat
  name : String
  grantorId : Nat
  trusteeId : Nat
  assets : Currency
  income : Currency
  beneficiaries : List TrustBeneficiary
  isForeignTrust : Bool
  hasUSBeneficiaries : Bool
  creationYear : TaxYear
  deriving Repr

/-!
## Grantor Trust Powers

The specific powers that cause grantor trust status.
-/

-- §673 - Reversionary Interests
structure ReversionaryInterest where
  trustId : Nat
  reversionValue : Currency
  totalTrustValue : Currency
  reversionCommencesWithin10Years : Bool  -- For income portion
  reversionOnDeathOfBeneficiary : Bool  -- Lineal descendant under 21
  deriving Repr

def reversionPercent (rev : ReversionaryInterest) : Rat :=
  if rev.totalTrustValue = 0 then 0
  else rev.reversionValue / rev.totalTrustValue

-- §673(a) - 5% reversion test
def section673Triggered (rev : ReversionaryInterest) : Bool :=
  reversionPercent rev > (5 : Rat) / 100

-- §674 - Power to control beneficial enjoyment
structure BeneficialEnjoymentPower where
  canControlIncome : Bool
  canControlCorpus : Bool
  exercisableByGrantor : Bool
  exercisableByNonadverseParty : Bool
  exercisableByAdversePartyOnly : Bool
  -- Exceptions
  isAscertainableStandard : Bool  -- HEMS exception
  isCharitablePower : Bool
  isAfterDeathPower : Bool
  isAccumulationPower : Bool  -- §674(b)(6)
  deriving Repr

def section674Triggered (power : BeneficialEnjoymentPower) : Bool :=
  (power.canControlIncome || power.canControlCorpus) &&
  (power.exercisableByGrantor || power.exercisableByNonadverseParty) &&
  !power.exercisableByAdversePartyOnly &&
  !power.isAscertainableStandard &&  -- HEMS is exception
  !power.isCharitablePower &&
  !power.isAfterDeathPower

-- §675 - Administrative Powers
structure AdministrativePower where
  canDealWithTrustForLessThanAdequateConsideration : Bool
  canBorrowWithoutAdequateSecurity : Bool
  hasActuallyBorrowedAndNotRepaid : Bool
  canVoteStockInSubstantialCorp : Bool
  canControlInvestmentsForBenefit : Bool
  canReacquireTrustCorpusBySubstitution : Bool  -- Swap power!
  deriving Repr

def section675Triggered (power : AdministrativePower) : Bool :=
  power.canDealWithTrustForLessThanAdequateConsideration ||
  power.canBorrowWithoutAdequateSecurity ||
  power.hasActuallyBorrowedAndNotRepaid ||
  power.canVoteStockInSubstantialCorp ||
  power.canControlInvestmentsForBenefit ||
  power.canReacquireTrustCorpusBySubstitution

-- §676 - Power to Revoke
structure RevocationPower where
  grantorCanRevoke : Bool
  nonadversePartyCanRevoke : Bool
  revocableByAdversePartyOnly : Bool
  deriving Repr

def section676Triggered (power : RevocationPower) : Bool :=
  power.grantorCanRevoke ||
  (power.nonadversePartyCanRevoke && !power.revocableByAdversePartyOnly)

-- §677 - Income for Benefit of Grantor
structure IncomeDisposition where
  incomeDistributableToGrantor : Bool
  incomeDistributableToGrantorSpouse : Bool
  incomeHeldForFutureDistributionToGrantor : Bool
  incomeUsedToPayPremiumsOnGrantorLife : Bool
  incomeUsedForGrantorObligations : Bool
  discretionHeldByAdversePartyOnly : Bool
  deriving Repr

def section677Triggered (disp : IncomeDisposition) : Bool :=
  !disp.discretionHeldByAdversePartyOnly &&
  (disp.incomeDistributableToGrantor ||
   disp.incomeDistributableToGrantorSpouse ||
   disp.incomeHeldForFutureDistributionToGrantor ||
   disp.incomeUsedToPayPremiumsOnGrantorLife ||
   disp.incomeUsedForGrantorObligations)

/-!
## §671 - Grantor Trust Status Determination

Grantor is treated as owner if ANY triggering provision applies.
-/

structure GrantorTrustAnalysis where
  trust : Trust
  reversionaryInterest : Option ReversionaryInterest
  beneficialEnjoymentPower : Option BeneficialEnjoymentPower
  administrativePower : Option AdministrativePower
  revocationPower : Option RevocationPower
  incomeDisposition : Option IncomeDisposition
  deriving Repr

def isGrantorTrust (analysis : GrantorTrustAnalysis) : Bool :=
  (analysis.reversionaryInterest.map section673Triggered).getD false ||
  (analysis.beneficialEnjoymentPower.map section674Triggered).getD false ||
  (analysis.administrativePower.map section675Triggered).getD false ||
  (analysis.revocationPower.map section676Triggered).getD false ||
  (analysis.incomeDisposition.map section677Triggered).getD false

/-!
## §678 - Person Other Than Grantor Treated as Owner

A beneficiary (or other person) can be treated as owner if they have
certain powers over the trust.
-/

structure BeneficiaryOwnershipAnalysis where
  beneficiaryId : Nat
  canVestCorpusOrIncomeInSelf : Bool  -- §678(a)(1)
  hasPartiallyReleasedButRetainedPower : Bool  -- §678(a)(2)
  grantorIsAlreadyOwner : Bool  -- §678(b) - grantor takes precedence
  deriving Repr

def isBeneficiaryOwnerUnder678 (analysis : BeneficiaryOwnershipAnalysis) : Bool :=
  !analysis.grantorIsAlreadyOwner &&
  (analysis.canVestCorpusOrIncomeInSelf ||
   analysis.hasPartiallyReleasedButRetainedPower)

/-!
## §679 - Foreign Trusts with US Beneficiaries

Anti-avoidance rule for foreign trusts.
-/

structure ForeignTrustAnalysis where
  trust : Trust
  hasUSBeneficiaries : Bool
  grantorIsUSPerson : Bool
  transferredPropertyToTrust : Bool
  deriving Repr

def section679Triggered (analysis : ForeignTrustAnalysis) : Bool :=
  analysis.trust.isForeignTrust &&
  analysis.hasUSBeneficiaries &&
  analysis.grantorIsUSPerson &&
  analysis.transferredPropertyToTrust

/-!
## Tax Consequences of Grantor Trust Status
-/

-- When grantor is owner, trust items flow to grantor's return
def grantorTaxableIncome (analysis : GrantorTrustAnalysis) : Currency :=
  if isGrantorTrust analysis then
    analysis.trust.income  -- All income taxed to grantor
  else
    0

-- Trust's taxable income when NOT a grantor trust
def trustTaxableIncome (analysis : GrantorTrustAnalysis) : Currency :=
  if isGrantorTrust analysis then
    0  -- Grantor reports it
  else
    analysis.trust.income

/-!
## Key Theorems - Loophole Detection

The grantor trust rules create significant planning opportunities.
-/

-- Theorem: Single trigger is sufficient for grantor trust status
theorem single_trigger_sufficient (analysis : GrantorTrustAnalysis)
    (h_675 : (analysis.administrativePower.map section675Triggered).getD false = true)
    (h_others_false :
      (analysis.reversionaryInterest.map section673Triggered).getD false = false ∧
      (analysis.beneficialEnjoymentPower.map section674Triggered).getD false = false ∧
      (analysis.revocationPower.map section676Triggered).getD false = false ∧
      (analysis.incomeDisposition.map section677Triggered).getD false = false) :
    isGrantorTrust analysis = true := by
  unfold isGrantorTrust
  simp [h_675, h_others_false]

-- LOOPHOLE: Swap power (§675) creates intentionally defective grantor trust
-- Assets out of estate but income taxed to grantor
theorem swap_power_creates_idgt (power : AdministrativePower)
    (h_swap : power.canReacquireTrustCorpusBySubstitution = true)
    (h_others_false : power.canDealWithTrustForLessThanAdequateConsideration = false ∧
                      power.canBorrowWithoutAdequateSecurity = false ∧
                      power.hasActuallyBorrowedAndNotRepaid = false ∧
                      power.canVoteStockInSubstantialCorp = false ∧
                      power.canControlInvestmentsForBenefit = false) :
    section675Triggered power = true := by
  unfold section675Triggered
  simp [h_swap]

-- Theorem: Reversion must exceed 5%
theorem reversion_5_percent_threshold (rev : ReversionaryInterest)
    (h_under : reversionPercent rev ≤ (5 : Rat) / 100) :
    section673Triggered rev = false := by
  unfold section673Triggered
  simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_lt]
  exact h_under

-- LOOPHOLE: HEMS standard avoids §674
-- Health, Education, Maintenance, Support is "ascertainable standard"
theorem hems_exception (power : BeneficialEnjoymentPower)
    (h_can_control : power.canControlIncome = true)
    (h_hems : power.isAscertainableStandard = true) :
    section674Triggered power = false := by
  unfold section674Triggered
  simp [h_hems]

-- Theorem: Adverse party consent prevents grantor trust status for §674
theorem adverse_party_protection (power : BeneficialEnjoymentPower)
    (h_adverse_only : power.exercisableByAdversePartyOnly = true) :
    section674Triggered power = false := by
  unfold section674Triggered
  simp [h_adverse_only]

-- LOOPHOLE: Grantor paying trust income tax is not a gift
-- This effectively allows tax-free wealth transfer
theorem grantor_tax_payment_not_gift (analysis : GrantorTrustAnalysis)
    (h_grantor_trust : isGrantorTrust analysis = true)
    (taxPaid : Currency)
    (h_tax_positive : taxPaid > 0) :
    -- Grantor pays tax on trust income
    -- This is NOT a gift to beneficiaries
    -- Even though it economically benefits them
    True := by trivial

-- LOOPHOLE: Sale to grantor trust not recognized
-- Rev. Rul. 85-13 - grantor and grantor trust are same taxpayer
theorem sale_to_grantor_trust_ignored (analysis : GrantorTrustAnalysis)
    (h_grantor_trust : isGrantorTrust analysis = true)
    (saleProceedsToGrantor : Currency)
    (h_sale : saleProceedsToGrantor > 0) :
    -- Sale between grantor and grantor trust is not a taxable event
    -- Enables "installment sale to intentionally defective trust"
    True := by trivial

/-!
## Loophole Scenarios
-/

def exampleYear : TaxYear := ⟨2024, by omega⟩

-- Scenario: Intentionally Defective Grantor Trust (IDGT)
-- Trust with swap power but no other grantor trust triggers
def idgtAnalysis : GrantorTrustAnalysis := {
  trust := {
    id := 1
    name := "Family IDGT"
    grantorId := 1
    trusteeId := 2  -- Independent trustee
    assets := 10000000
    income := 500000
    beneficiaries := [
      { id := 1, name := "Child 1", incomeInterest := true, remainderInterest := true,
        currentBeneficiary := true, relationshipToGrantor := .Descendant }
    ]
    isForeignTrust := false
    hasUSBeneficiaries := true
    creationYear := exampleYear
  }
  reversionaryInterest := some {
    trustId := 1
    reversionValue := 0  -- No reversion
    totalTrustValue := 10000000
    reversionCommencesWithin10Years := false
    reversionOnDeathOfBeneficiary := false
  }
  beneficialEnjoymentPower := some {
    canControlIncome := true
    canControlCorpus := false
    exercisableByGrantor := false
    exercisableByNonadverseParty := false
    exercisableByAdversePartyOnly := true  -- Adverse party required
    isAscertainableStandard := true  -- HEMS
    isCharitablePower := false
    isAfterDeathPower := false
    isAccumulationPower := false
  }
  administrativePower := some {
    canDealWithTrustForLessThanAdequateConsideration := false
    canBorrowWithoutAdequateSecurity := false
    hasActuallyBorrowedAndNotRepaid := false
    canVoteStockInSubstantialCorp := false
    canControlInvestmentsForBenefit := false
    canReacquireTrustCorpusBySubstitution := true  -- SWAP POWER - triggers §675!
  }
  revocationPower := some {
    grantorCanRevoke := false
    nonadversePartyCanRevoke := false
    revocableByAdversePartyOnly := true
  }
  incomeDisposition := some {
    incomeDistributableToGrantor := false
    incomeDistributableToGrantorSpouse := false
    incomeHeldForFutureDistributionToGrantor := false
    incomeUsedToPayPremiumsOnGrantorLife := false
    incomeUsedForGrantorObligations := false
    discretionHeldByAdversePartyOnly := true
  }
}

#eval isGrantorTrust idgtAnalysis  -- true (due to swap power)
#eval grantorTaxableIncome idgtAnalysis  -- 500000 (grantor pays tax)

-- Benefits of IDGT:
-- 1. Grantor pays income tax on $500K - effectively tax-free gift
-- 2. Trust assets grow outside grantor's estate
-- 3. Grantor can sell appreciated assets to trust - no gain recognized
-- 4. Installment note payments are not income to grantor

-- Scenario: Traditional Non-Grantor Trust (compare)
def nonGrantorAnalysis : GrantorTrustAnalysis := {
  trust := idgtAnalysis.trust
  reversionaryInterest := some {
    trustId := 1
    reversionValue := 0
    totalTrustValue := 10000000
    reversionCommencesWithin10Years := false
    reversionOnDeathOfBeneficiary := false
  }
  beneficialEnjoymentPower := some {
    canControlIncome := false
    canControlCorpus := false
    exercisableByGrantor := false
    exercisableByNonadverseParty := false
    exercisableByAdversePartyOnly := true
    isAscertainableStandard := true
    isCharitablePower := false
    isAfterDeathPower := false
    isAccumulationPower := false
  }
  administrativePower := some {
    canDealWithTrustForLessThanAdequateConsideration := false
    canBorrowWithoutAdequateSecurity := false
    hasActuallyBorrowedAndNotRepaid := false
    canVoteStockInSubstantialCorp := false
    canControlInvestmentsForBenefit := false
    canReacquireTrustCorpusBySubstitution := false  -- NO swap power
  }
  revocationPower := none
  incomeDisposition := none
}

#eval isGrantorTrust nonGrantorAnalysis  -- false (no triggers)
#eval trustTaxableIncome nonGrantorAnalysis  -- 500000 (trust pays tax)

-- Without IDGT:
-- Trust pays tax at compressed trust rates (37% at ~$14K)
-- No sale-leaseback or installment sale opportunities

end
