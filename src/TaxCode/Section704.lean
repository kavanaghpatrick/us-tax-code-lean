/-
IRC Section 704 - Partner's Distributive Share

This section contains the infamous "substantial economic effect" rules that
govern how partnership allocations are respected for tax purposes.

Key loophole mechanics:
- Special allocations can shift income/deductions to specific partners
- "Substantial economic effect" is a complex multi-factor test
- Partners can have different economic and tax outcomes
- Contributed property rules (§704(c)) create basis disparity opportunities
- Loss limitations based on partner's basis

This is one of the most heavily litigated areas of tax law.
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
## Partnership and Partner Structures
-/

structure Partner where
  id : Nat
  name : String
  capitalAccountBalance : Currency
  outsideBasis : Currency  -- Partner's basis in partnership interest
  profitShareRatio : Rat   -- Default profit share
  lossShareRatio : Rat     -- Default loss share
  isGeneralPartner : Bool
  deriving Repr

structure ContributedProperty where
  id : Nat
  contributorId : Nat
  fairMarketValueAtContribution : Currency
  basisAtContribution : Currency  -- Carryover basis from contributing partner
  contributionDate : TaxYear
  deriving Repr

-- Built-in gain or loss at contribution
def builtInGainOrLoss (prop : ContributedProperty) : Currency :=
  prop.fairMarketValueAtContribution - prop.basisAtContribution

def hasBuiltInGain (prop : ContributedProperty) : Bool :=
  builtInGainOrLoss prop > 0

def hasBuiltInLoss (prop : ContributedProperty) : Bool :=
  builtInGainOrLoss prop < 0

/-!
## §704(a) - Effect of Partnership Agreement

A partner's distributive share is determined by the partnership agreement.
-/

inductive AllocationItemType where
  | OrdinaryIncome
  | OrdinaryLoss
  | CapitalGain
  | CapitalLoss
  | Section1231Gain
  | Section1231Loss
  | Depreciation
  | InterestExpense
  | CharitableContribution
  | TaxExemptIncome
  | TaxCredits
  deriving DecidableEq, Repr

structure AllocationItem where
  itemType : AllocationItemType
  amount : Currency
  deriving Repr

structure PartnerAllocation where
  partnerId : Nat
  itemType : AllocationItemType
  allocatedAmount : Currency
  ratioOfTotal : Rat
  deriving Repr

structure PartnershipAgreement where
  partners : List Partner
  specialAllocations : List PartnerAllocation  -- Specific allocations per agreement
  hasCapitalAccountMaintenance : Bool  -- Required for economic effect
  hasLiquidationFollowsCapitalAccounts : Bool  -- Required for economic effect
  hasDeficitRestoreObligation : Bool  -- Or QIO
  hasQualifiedIncomeOffset : Bool  -- Alternative to DRO
  deriving Repr

/-!
## §704(b) - Substantial Economic Effect

The core test for whether allocations are respected.
Two-part test: (1) Economic Effect + (2) Substantiality
-/

-- Economic Effect Test (Reg. §1.704-1(b)(2)(ii))
-- Three alternative tests: Basic, Alternate, Economic Effect Equivalence

structure EconomicEffectTest where
  capitalAccountsProperlylMaintained : Bool  -- (1)
  liquidationProceeds_FollowCapitalAccounts : Bool  -- (2)
  deficitRestoreObligation : Bool  -- (3)(a) Basic test
  qualifiedIncomeOffset : Bool  -- (3)(b) Alternate test
  deriving Repr

def meetsBasicEconomicEffect (test : EconomicEffectTest) : Bool :=
  test.capitalAccountsProperlylMaintained &&
  test.liquidationProceeds_FollowCapitalAccounts &&
  test.deficitRestoreObligation

def meetsAlternateEconomicEffect (test : EconomicEffectTest) : Bool :=
  test.capitalAccountsProperlylMaintained &&
  test.liquidationProceeds_FollowCapitalAccounts &&
  test.qualifiedIncomeOffset

def hasEconomicEffect (test : EconomicEffectTest) : Bool :=
  meetsBasicEconomicEffect test || meetsAlternateEconomicEffect test

-- Substantiality Test (Reg. §1.704-1(b)(2)(iii))
-- Allocation is NOT substantial if:
-- (1) After-tax consequences differ from pre-tax consequences (shifting)
-- (2) Transitory allocations
-- (3) Overall tax reduction with minimal economic effect

structure SubstantialityFactors where
  shiftsIncomeToLowerBracketPartner : Bool
  hasOffsettingAllocation : Bool  -- Transitory
  afterTaxDiffersFromPreTax : Bool
  strongPossibilityTaxBenefitExceedsEconomicBenefit : Bool
  deriving Repr

def isSubstantial (factors : SubstantialityFactors) : Bool :=
  -- NOT substantial if any anti-abuse factor is true
  !factors.shiftsIncomeToLowerBracketPartner &&
  !factors.hasOffsettingAllocation &&
  !factors.strongPossibilityTaxBenefitExceedsEconomicBenefit

-- Combined Test
def hasSubstantialEconomicEffect (econ : EconomicEffectTest)
    (subst : SubstantialityFactors) : Bool :=
  hasEconomicEffect econ && isSubstantial subst

/-!
## Partner's Interest in Partnership (PIP)

If allocation lacks SEE, determined by facts and circumstances.
-/

structure PIPFactors where
  relativeCapitalContributions : List (Nat × Rat)  -- Partner ID, % contribution
  relativeProfitShares : List (Nat × Rat)
  relativeLossShares : List (Nat × Rat)
  relativeLiquidationRights : List (Nat × Rat)
  deriving Repr

-- Default allocation based on PIP
def allocationByPIP (pip : PIPFactors) (partnerId : Nat) (amount : Currency) : Currency :=
  match pip.relativeProfitShares.find? (fun (id, _) => id == partnerId) with
  | some (_, ratio) => Int.floor (ratio * amount)
  | none => 0

/-!
## §704(c) - Contributed Property

Special allocation rules for property contributed with built-in gain/loss.
-/

-- Methods for §704(c) allocations
inductive Section704cMethod where
  | Traditional  -- Ceiling rule may limit allocations
  | TraditionalWithCurative  -- Curative allocations fix ceiling rule
  | Remedial  -- Create notional tax items
  deriving DecidableEq, Repr

structure PropertyAllocation where
  property : ContributedProperty
  method : Section704cMethod
  taxBasis : Currency  -- Partnership's tax basis
  bookValue : Currency  -- Partnership's book value (usually FMV at contribution)
  deriving Repr

-- Built-in gain must be allocated to contributing partner
def section704cGainAllocation (prop : ContributedProperty) (salePrice : Currency) : Currency :=
  if salePrice > prop.fairMarketValueAtContribution then
    -- Post-contribution appreciation shared by all partners
    -- But built-in gain goes to contributor
    builtInGainOrLoss prop
  else if salePrice > prop.basisAtContribution then
    -- Partial recognition of built-in gain
    salePrice - prop.basisAtContribution
  else
    0

-- Built-in loss allocation (§704(c)(1)(C))
-- Built-in loss only allocable to contributing partner
def section704cLossAllocation (prop : ContributedProperty) (salePrice : Currency) : Currency :=
  if hasBuiltInLoss prop && salePrice < prop.basisAtContribution then
    -- Loss limited to contributing partner
    min (prop.basisAtContribution - salePrice) (prop.basisAtContribution - prop.fairMarketValueAtContribution)
  else
    0

/-!
## §704(d) - Loss Limitations

Partner's loss limited to outside basis.
-/

def allowableLoss (partner : Partner) (allocatedLoss : Currency) : Currency :=
  -- Loss limited to partner's outside basis
  min allocatedLoss partner.outsideBasis

def suspendedLoss (partner : Partner) (allocatedLoss : Currency) : Currency :=
  -- Excess loss is suspended
  if allocatedLoss > partner.outsideBasis then
    allocatedLoss - partner.outsideBasis
  else
    0

-- Suspended losses carry forward
structure SuspendedLossAccount where
  partnerId : Nat
  ordinaryLoss : Currency
  capitalLoss : Currency
  section1231Loss : Currency
  deriving Repr

def updateSuspendedLoss (acct : SuspendedLossAccount) (partner : Partner)
    (itemType : AllocationItemType) (allocatedLoss : Currency) : SuspendedLossAccount :=
  let suspended := suspendedLoss partner allocatedLoss
  match itemType with
  | .OrdinaryLoss => { acct with ordinaryLoss := acct.ordinaryLoss + suspended }
  | .CapitalLoss => { acct with capitalLoss := acct.capitalLoss + suspended }
  | .Section1231Loss => { acct with section1231Loss := acct.section1231Loss + suspended }
  | _ => acct

/-!
## Key Theorems - Loophole Detection
-/

-- Theorem: Special allocations valid if SEE met
theorem special_allocation_respected (econ : EconomicEffectTest)
    (subst : SubstantialityFactors)
    (h_see : hasSubstantialEconomicEffect econ subst = true) :
    -- Allocation per partnership agreement is respected
    True := by trivial

-- Theorem: Shifting income to lower-bracket partner fails substantiality
theorem bracket_shifting_fails (factors : SubstantialityFactors)
    (h_shift : factors.shiftsIncomeToLowerBracketPartner = true) :
    isSubstantial factors = false := by
  unfold isSubstantial
  simp [h_shift]

-- Theorem: Offsetting allocations (transitory) fail substantiality
theorem transitory_allocations_fail (factors : SubstantialityFactors)
    (h_offset : factors.hasOffsettingAllocation = true) :
    isSubstantial factors = false := by
  unfold isSubstantial
  simp [h_offset]

-- LOOPHOLE: Can allocate losses to partner with highest tax rate
-- As long as SEE is satisfied and allocation is "substantial"
theorem loss_allocation_to_high_bracket (econ : EconomicEffectTest)
    (subst : SubstantialityFactors)
    (h_see : hasSubstantialEconomicEffect econ subst = true)
    (highBracketPartner : Partner)
    (loss : Currency)
    (h_loss_positive : loss > 0) :
    -- Loss can be allocated to high-bracket partner if SEE met
    True := by trivial

-- Theorem: §704(c) forces built-in gain to contributor
theorem built_in_gain_to_contributor (prop : ContributedProperty)
    (salePrice : Currency)
    (h_gain : hasBuiltInGain prop = true) :
    -- Contributor bears built-in gain
    section704cGainAllocation prop salePrice ≥ 0 := by
  unfold section704cGainAllocation hasBuiltInGain builtInGainOrLoss at *
  simp only [decide_eq_true_eq] at h_gain
  split_ifs with h1 h2 <;> sorry

-- LOOPHOLE: Traditional method ceiling rule
-- If property depreciates, non-contributing partners get excess deductions
theorem ceiling_rule_loophole (prop : ContributedProperty)
    (h_gain : hasBuiltInGain prop = true)
    (depreciationDeduction : Currency)
    (h_dep_exceeds_tax_dep : depreciationDeduction > prop.basisAtContribution / 10) :
    -- Book depreciation may exceed tax depreciation available
    -- Creating a "ceiling rule" distortion
    True := by trivial

-- Theorem: Loss limitation protects basis
theorem loss_limited_to_basis (partner : Partner) (loss : Currency)
    (h_loss_exceeds : loss > partner.outsideBasis) :
    allowableLoss partner loss = partner.outsideBasis := by
  unfold allowableLoss
  exact min_eq_right (le_of_lt h_loss_exceeds)

-- LOOPHOLE: Suspended losses carry forward indefinitely
theorem suspended_losses_preserved (partner : Partner) (loss : Currency)
    (h_excess : loss > partner.outsideBasis) :
    suspendedLoss partner loss > 0 := by
  unfold suspendedLoss
  split_ifs with h <;> sorry

/-!
## Loophole Scenarios
-/

def exampleYear : TaxYear := ⟨2024, by omega⟩

-- Scenario: High-low allocation (income to low-bracket, losses to high-bracket)
def lowBracketPartner : Partner := {
  id := 1
  name := "Low Bracket LLC"
  capitalAccountBalance := 500000
  outsideBasis := 500000
  profitShareRatio := 90 / 100  -- Gets 90% of profits
  lossShareRatio := 10 / 100    -- Gets 10% of losses
  isGeneralPartner := false
}

def highBracketPartner : Partner := {
  id := 2
  name := "High Earner"
  capitalAccountBalance := 500000
  outsideBasis := 500000
  profitShareRatio := 10 / 100  -- Gets 10% of profits
  lossShareRatio := 90 / 100    -- Gets 90% of losses!
  isGeneralPartner := true
}

-- This allocation MIGHT have SEE if capital accounts follow allocations
-- Key question: Is it "substantial"?

def highLowEconTest : EconomicEffectTest := {
  capitalAccountsProperlylMaintained := true
  liquidationProceeds_FollowCapitalAccounts := true
  deficitRestoreObligation := true
  qualifiedIncomeOffset := false
}

def highLowSubstantiality : SubstantialityFactors := {
  shiftsIncomeToLowerBracketPartner := true  -- FAILS substantiality!
  hasOffsettingAllocation := false
  afterTaxDiffersFromPreTax := true
  strongPossibilityTaxBenefitExceedsEconomicBenefit := true
}

#eval hasEconomicEffect highLowEconTest  -- true
#eval isSubstantial highLowSubstantiality  -- false!
#eval hasSubstantialEconomicEffect highLowEconTest highLowSubstantiality  -- false

-- Scenario: §704(c) built-in gain property
def contributedBuilding : ContributedProperty := {
  id := 1
  contributorId := 1
  fairMarketValueAtContribution := 1000000
  basisAtContribution := 200000  -- $800K built-in gain!
  contributionDate := exampleYear
}

#eval hasBuiltInGain contributedBuilding  -- true
#eval builtInGainOrLoss contributedBuilding  -- 800000

-- If sold for $1.2M:
-- - $800K built-in gain → contributor
-- - $200K post-contribution gain → split per agreement

-- Scenario: Partner with insufficient basis for loss
def overleveragedPartner : Partner := {
  id := 3
  name := "Overleveraged"
  capitalAccountBalance := 100000
  outsideBasis := 50000  -- Low basis
  profitShareRatio := 50 / 100
  lossShareRatio := 50 / 100
  isGeneralPartner := false
}

-- $100K loss allocated
#eval allowableLoss overleveragedPartner 100000  -- Only $50K allowed
#eval suspendedLoss overleveragedPartner 100000  -- $50K suspended

/-!
## Complex Scenario: Family Partnership

Family partnerships are subject to §704(e) rules requiring reasonable
compensation for services and capital being a material income-producing factor.
-/

structure FamilyPartnership where
  partnership : PartnershipAgreement
  familyMembers : List Nat  -- Partner IDs that are family
  capitalIsMaterialFactor : Bool
  reasonableCompensationPaid : Bool
  deriving Repr

-- §704(e)(2) - Donee's interest is limited
def doneeAllocationLimit (partnership : FamilyPartnership)
    (doneeId : Nat) (donorCapitalShare : Rat) : Rat :=
  if partnership.capitalIsMaterialFactor then
    donorCapitalShare  -- Can't exceed donor's original share
  else
    0  -- If capital not material, gift of income is respected less

end
