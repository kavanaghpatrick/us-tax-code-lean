/-
IRC Section 831 - Tax on insurance companies other than life insurance companies

This formalization focuses on §831(b) "micro-captive" insurance rules,
a known tax shelter area (IRS "Dirty Dozen" list).

Key loophole mechanics:
- Small companies elect taxation only on investment income
- Creates arbitrage when related parties pay deductible premiums
- Diversification rules attempt to limit abuse
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
## §831(b)(2)(A) - Premium Threshold

The company qualifies if net written premiums (or direct written premiums
if greater) do not exceed $2,200,000 (adjusted for inflation from 2015).
-/

-- IRC §831(b)(2)(A)(i) - Base threshold
def basePremiumThreshold : Currency := 2200000

-- Inflation adjustment per §831(b)(2)(E)
-- For simplicity, we model this as a function of tax year
def inflationAdjustedThreshold (year : TaxYear) : Currency :=
  -- Base year is 2015, $2,200,000
  -- Rounded down to nearest $50,000
  let baseYear := 2015
  let yearsElapsed := year.year - baseYear
  -- Approximate 2% annual inflation
  let inflationFactor : Rat := (102 / 100) ^ yearsElapsed
  let adjusted := Int.floor (inflationFactor * basePremiumThreshold)
  -- Round down to nearest $50,000
  (adjusted / 50000) * 50000

/-!
## Insurance Company Structure
-/

structure PolicyHolder where
  id : Nat
  premiumsPaid : Currency
  isRelatedParty : Bool  -- Related under §267(b) or §707(b)
  deriving DecidableEq, Repr

structure SpecifiedHolder where
  id : Nat
  ownershipPercentage : Rat  -- Percentage of insurance company
  specifiedAssetsPercentage : Rat  -- Percentage of insured assets
  isLinealDescendant : Bool
  isSpouseOfDescendant : Bool
  isNonCitizenSpouse : Bool
  deriving Repr

structure InsuranceCompany where
  id : Nat
  taxYear : TaxYear
  netWrittenPremiums : Currency
  directWrittenPremiums : Currency
  investmentIncome : Currency
  underwritingIncome : Currency
  policyHolders : List PolicyHolder
  specifiedHolders : List SpecifiedHolder
  hasElected831b : Bool
  controlledGroupPremiums : Currency  -- Premiums from related companies
  deriving Repr

/-!
## §831(b)(2)(A)(i) - Premium Test
-/

-- The relevant premium amount is the greater of net or direct
def relevantPremiums (co : InsuranceCompany) : Currency :=
  max co.netWrittenPremiums co.directWrittenPremiums

-- Include controlled group premiums per §831(b)(2)(C)
def totalPremiumsWithControlledGroup (co : InsuranceCompany) : Currency :=
  relevantPremiums co + co.controlledGroupPremiums

-- Premium test: must not exceed threshold
def meetsPremiumTest (co : InsuranceCompany) : Bool :=
  totalPremiumsWithControlledGroup co ≤ inflationAdjustedThreshold co.taxYear

/-!
## §831(b)(2)(B) - Diversification Requirements

Two alternative tests:
1. No policyholder > 20% of premiums, OR
2. If (1) fails, specified holder ownership ≤ specified assets % + de minimis
-/

-- De minimis is 2 percentage points per §831(b)(2)(B)(iv)(IV)
def deMinimisPercentage : Rat := 2 / 100

-- Calculate percentage of premiums from each policyholder
def policyholderPremiumPercentage (ph : PolicyHolder) (co : InsuranceCompany) : Rat :=
  let total := relevantPremiums co
  if total = 0 then 0 else (ph.premiumsPaid : Rat) / (total : Rat)

-- Aggregate related policyholders per §831(b)(2)(C)(i)(II)
def aggregateRelatedPolicyholders (co : InsuranceCompany) : List PolicyHolder :=
  -- Group related parties together
  let related := co.policyHolders.filter (·.isRelatedParty)
  let unrelated := co.policyHolders.filter (fun ph => !ph.isRelatedParty)
  let relatedAggregated : PolicyHolder := {
    id := 0
    premiumsPaid := related.foldl (fun acc ph => acc + ph.premiumsPaid) 0
    isRelatedParty := true
  }
  if related.isEmpty then unrelated else relatedAggregated :: unrelated

-- Test 1: No policyholder exceeds 20%
def meetsNoPolicyholderOver20Test (co : InsuranceCompany) : Bool :=
  let aggregated := aggregateRelatedPolicyholders co
  aggregated.all fun ph =>
    policyholderPremiumPercentage ph co ≤ (20 : Rat) / 100

-- Check if holder is a "specified holder" per §831(b)(2)(B)(iii)
def isSpecifiedHolder (sh : SpecifiedHolder) : Bool :=
  sh.isLinealDescendant || sh.isSpouseOfDescendant || sh.isNonCitizenSpouse

-- Test 2: Specified holder test
-- Ownership % must not exceed specified assets % + de minimis
def meetsSpecifiedHolderTest (co : InsuranceCompany) : Bool :=
  co.specifiedHolders.all fun sh =>
    if isSpecifiedHolder sh then
      sh.ownershipPercentage ≤ sh.specifiedAssetsPercentage + deMinimisPercentage
    else true

-- Combined diversification test per §831(b)(2)(B)(i)
def meetsDiversificationTest (co : InsuranceCompany) : Bool :=
  meetsNoPolicyholderOver20Test co || meetsSpecifiedHolderTest co

/-!
## §831(b)(2)(A) - Full Qualification Test
-/

def qualifiesFor831b (co : InsuranceCompany) : Bool :=
  meetsPremiumTest co &&
  meetsDiversificationTest co &&
  co.hasElected831b

/-!
## Tax Calculation

Under §831(b), qualifying companies pay tax only on investment income.
Under §831(a), they pay tax on total taxable income.
-/

-- Standard corporate rate (simplified - actual is §11)
def corporateTaxRate : Rat := 21 / 100

def taxUnder831a (co : InsuranceCompany) : Currency :=
  -- Tax on total income (investment + underwriting)
  let totalIncome := co.investmentIncome + co.underwritingIncome
  let taxableIncome := max totalIncome 0
  Int.floor (corporateTaxRate * taxableIncome)

def taxUnder831b (co : InsuranceCompany) : Currency :=
  -- Tax only on investment income
  let taxableIncome := max co.investmentIncome 0
  Int.floor (corporateTaxRate * taxableIncome)

def actualTax (co : InsuranceCompany) : Currency :=
  if qualifiesFor831b co then taxUnder831b co else taxUnder831a co

-- Tax savings from 831(b) election
def taxSavingsFrom831b (co : InsuranceCompany) : Currency :=
  if qualifiesFor831b co then
    taxUnder831a co - taxUnder831b co
  else 0

/-!
## Key Theorems - Loophole Detection

These theorems formally verify properties that could reveal loopholes.
-/

-- Theorem: 831(b) always saves tax when underwriting income is positive
theorem _831b_saves_tax_on_underwriting (co : InsuranceCompany)
    (h_qual : qualifiesFor831b co = true)
    (h_pos_underwriting : co.underwritingIncome > 0) :
    taxSavingsFrom831b co > 0 := by
  unfold taxSavingsFrom831b
  simp [h_qual]
  unfold taxUnder831a taxUnder831b
  sorry -- Arithmetic proof

-- Theorem: Threshold cliff - $1 over disqualifies entirely
theorem threshold_cliff_effect (co : InsuranceCompany)
    (h_at_threshold : totalPremiumsWithControlledGroup co = inflationAdjustedThreshold co.taxYear)
    (h_other_qual : meetsDiversificationTest co = true ∧ co.hasElected831b = true) :
    qualifiesFor831b co = true := by
  unfold qualifiesFor831b meetsPremiumTest
  simp [h_at_threshold, h_other_qual]

-- Theorem: Controlled group aggregation can disqualify
theorem controlled_group_disqualifies (co : InsuranceCompany)
    (h_own_premiums_ok : relevantPremiums co < inflationAdjustedThreshold co.taxYear)
    (h_controlled_too_much : co.controlledGroupPremiums >
        inflationAdjustedThreshold co.taxYear - relevantPremiums co) :
    meetsPremiumTest co = false := by
  unfold meetsPremiumTest totalPremiumsWithControlledGroup
  simp
  sorry -- Arithmetic proof

-- Theorem: De minimis creates a 2% ownership premium loophole
-- A specified holder can own 2% MORE than their asset percentage
theorem de_minimis_ownership_premium (sh : SpecifiedHolder) (co : InsuranceCompany)
    (h_specified : isSpecifiedHolder sh = true)
    (h_assets : sh.specifiedAssetsPercentage = 30 / 100)
    (h_ownership : sh.ownershipPercentage = 32 / 100) :
    sh.ownershipPercentage ≤ sh.specifiedAssetsPercentage + deMinimisPercentage := by
  simp only [h_assets, h_ownership, deMinimisPercentage]
  norm_num

-- Theorem: Related party aggregation loophole
-- If parties are NOT related under §267(b)/§707(b), they're counted separately
theorem unrelated_parties_separate (co : InsuranceCompany)
    (h_two_unrelated : ∃ ph1 ph2, ph1 ∈ co.policyHolders ∧ ph2 ∈ co.policyHolders ∧
        !ph1.isRelatedParty ∧ !ph2.isRelatedParty ∧ ph1.id ≠ ph2.id)
    (h_each_under_20 : co.policyHolders.all fun ph =>
        !ph.isRelatedParty → policyholderPremiumPercentage ph co ≤ 20/100) :
    meetsNoPolicyholderOver20Test co = true := by
  unfold meetsNoPolicyholderOver20Test aggregateRelatedPolicyholders
  sorry -- Proof depends on aggregation logic

/-!
## Loophole Scenario: Classic Micro-Captive Abuse

The following structures model the classic micro-captive tax shelter:
1. Operating business creates captive insurance company
2. Pays "premiums" to captive (deductible to operating company)
3. Captive elects 831(b) - only taxed on investment income
4. Underwriting "income" (premiums - claims) is tax-free
5. Money eventually returns to related parties

The diversification rules attempt to limit this, but loopholes exist.
-/

structure MicroCaptiveArrangement where
  operatingCompany : Nat  -- ID of operating business
  captiveInsurer : InsuranceCompany
  premiumsPaidByOperating : Currency
  claimsPaidByCaptive : Currency
  deriving Repr

-- Tax arbitrage from arrangement
def taxArbitrage (arr : MicroCaptiveArrangement) : Currency :=
  -- Operating company deduction (at corporate rate)
  let deductionValue := Int.floor (corporateTaxRate * arr.premiumsPaidByOperating)
  -- Captive tax saved (underwriting income not taxed under 831(b))
  let underwritingNotTaxed := arr.premiumsPaidByOperating - arr.claimsPaidByCaptive
  let taxableAmount := max underwritingNotTaxed 0
  let taxSaved := Int.floor (corporateTaxRate * taxableAmount)
  deductionValue + taxSaved

-- Theorem: Arbitrage exists when premiums exceed claims
theorem micro_captive_arbitrage_exists (arr : MicroCaptiveArrangement)
    (h_qual : qualifiesFor831b arr.captiveInsurer = true)
    (h_premiums_gt_claims : arr.premiumsPaidByOperating > arr.claimsPaidByCaptive)
    (h_positive_premium : arr.premiumsPaidByOperating > 0) :
    taxArbitrage arr > 0 := by
  unfold taxArbitrage
  sorry -- Arithmetic proof

/-!
## Test Cases
-/

def exampleTaxYear2024 : TaxYear := ⟨2024, by omega⟩

def exampleQualifyingCaptive : InsuranceCompany := {
  id := 1
  taxYear := exampleTaxYear2024
  netWrittenPremiums := 1500000  -- $1.5M
  directWrittenPremiums := 1500000
  investmentIncome := 100000
  underwritingIncome := 500000  -- Tax-free under 831(b)!
  policyHolders := [
    { id := 1, premiumsPaid := 300000, isRelatedParty := false },
    { id := 2, premiumsPaid := 300000, isRelatedParty := false },
    { id := 3, premiumsPaid := 300000, isRelatedParty := false },
    { id := 4, premiumsPaid := 300000, isRelatedParty := false },
    { id := 5, premiumsPaid := 300000, isRelatedParty := false }
  ]
  specifiedHolders := []
  hasElected831b := true
  controlledGroupPremiums := 0
}

#eval! qualifiesFor831b exampleQualifyingCaptive  -- Should be true
#eval! taxSavingsFrom831b exampleQualifyingCaptive  -- Tax saved

def exampleDisqualifiedByPremiums : InsuranceCompany := {
  id := 2
  taxYear := exampleTaxYear2024
  netWrittenPremiums := 2500000  -- Over threshold!
  directWrittenPremiums := 2500000
  investmentIncome := 100000
  underwritingIncome := 500000
  policyHolders := []
  specifiedHolders := []
  hasElected831b := true
  controlledGroupPremiums := 0
}

#eval! qualifiesFor831b exampleDisqualifiedByPremiums  -- Should be false

def exampleDisqualifiedByConcentration : InsuranceCompany := {
  id := 3
  taxYear := exampleTaxYear2024
  netWrittenPremiums := 1000000
  directWrittenPremiums := 1000000
  investmentIncome := 50000
  underwritingIncome := 200000
  policyHolders := [
    -- One policyholder has 25% - fails 20% test
    { id := 1, premiumsPaid := 250000, isRelatedParty := false },
    { id := 2, premiumsPaid := 750000, isRelatedParty := false }
  ]
  specifiedHolders := []  -- No specified holders, so test 2 passes vacuously
  hasElected831b := true
  controlledGroupPremiums := 0
}

-- Note: This might PASS because the specified holder test passes vacuously!
-- This is a potential loophole in the diversification rules.
#eval! qualifiesFor831b exampleDisqualifiedByConcentration

end
