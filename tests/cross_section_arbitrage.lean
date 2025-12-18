/-
CROSS-SECTION ARBITRAGE SEARCH

Look for entities that satisfy MULTIPLE beneficial qualifications simultaneously
from our formalized sections. The goal is to find combinations that might not
be obvious from reading any single section.
-/

import Mathlib

set_option linter.unusedVariables false
noncomputable section

abbrev Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq

/-!
## Simplified Multi-Section Entity

An entity that could potentially qualify under multiple sections.
-/

structure MultiEntity where
  -- Identity
  name : String

  -- Ownership structure
  usOwnershipPct : Rat           -- US persons' ownership
  foreignOwnershipPct : Rat      -- Foreign persons' ownership

  -- Income characteristics
  totalIncome : Currency
  passiveIncomePct : Rat         -- For PFIC test
  activeBusinessIncomePct : Rat  -- For CFC/Subpart F
  underwritingIncome : Currency  -- For §831
  investmentIncome : Currency

  -- Asset characteristics
  totalAssets : Currency
  passiveAssetsPct : Rat         -- For PFIC test
  qbai : Currency                -- Qualified Business Asset Investment (GILTI)
  insurancePremiums : Currency   -- For §831

  -- Entity type flags
  isForeignCorp : Bool
  isDomesticCorp : Bool
  isInsuranceCompany : Bool
  isQualifiedSmallBusiness : Bool
  isTrust : Bool
  isGrantorTrust : Bool

  -- Holding period
  yearsHeld : Nat

  deriving Repr

/-!
## Section Qualification Functions
-/

-- §831(b) Micro-Captive: Premiums ≤ $2.2M, insurance company
def qualifiesFor831b (e : MultiEntity) : Bool :=
  e.isInsuranceCompany &&
  e.insurancePremiums ≤ 2200000 &&
  e.isDomesticCorp

-- §951 CFC: Foreign corp, >50% US shareholder ownership
def isCFC (e : MultiEntity) : Bool :=
  e.isForeignCorp &&
  e.usOwnershipPct > 50/100

-- §1297 PFIC: 75% passive income OR 50% passive assets
def isPFIC (e : MultiEntity) : Bool :=
  e.isForeignCorp &&
  (e.passiveIncomePct ≥ 75/100 || e.passiveAssetsPct ≥ 50/100)

-- §1297(d) CFC Exemption from PFIC
def isCFCExemptFromPFIC (e : MultiEntity) : Bool :=
  isCFC e  -- If CFC, 10%+ US shareholders are exempt from PFIC

-- §951A High-Tax Exception (18.9% threshold)
def qualifiesForHighTaxException (foreignTaxRate : Rat) : Bool :=
  foreignTaxRate > 189/1000

-- §1202 QSBS: Qualified small business, held 5+ years
def qualifiesForQSBS (e : MultiEntity) : Bool :=
  e.isQualifiedSmallBusiness &&
  e.isDomesticCorp &&
  e.totalAssets ≤ 50000000 &&
  e.yearsHeld ≥ 5

-- §671 Grantor Trust
def isGrantorTrustQualified (e : MultiEntity) : Bool :=
  e.isTrust && e.isGrantorTrust

-- GILTI with QBAI offset (simplified)
def giltiReduction (e : MultiEntity) : Currency :=
  if isCFC e then e.qbai / 10 else 0  -- 10% deemed return excluded

/-!
## ARBITRAGE SEARCH: Find Multi-Qualifying Entities
-/

-- Score: How many beneficial qualifications does this entity have?
def benefitScore (e : MultiEntity) : Nat :=
  (if qualifiesFor831b e then 2 else 0) +
  (if isCFC e && !isPFIC e then 2 else 0) +  -- CFC without PFIC is good
  (if isCFCExemptFromPFIC e then 1 else 0) +
  (if qualifiesForQSBS e then 3 else 0) +     -- QSBS is very valuable
  (if isGrantorTrustQualified e then 2 else 0) +
  (if giltiReduction e > 0 then 1 else 0)

-- Is this entity in a "sweet spot" with multiple benefits?
def isArbitrage (e : MultiEntity) : Bool :=
  benefitScore e ≥ 4

/-!
## SPECIFIC ARBITRAGE SCENARIOS
-/

-- Scenario 1: Domestic captive that's also QSBS-eligible
-- Could you get §831(b) tax-free underwriting AND §1202 exclusion on sale?
def captiveQSBS : MultiEntity := {
  name := "Captive + QSBS Combo"
  usOwnershipPct := 100/100
  foreignOwnershipPct := 0
  totalIncome := 1000000
  passiveIncomePct := 10/100
  activeBusinessIncomePct := 90/100
  underwritingIncome := 500000
  investmentIncome := 100000
  totalAssets := 40000000  -- Under $50M QSBS limit
  passiveAssetsPct := 20/100
  qbai := 0
  insurancePremiums := 1500000  -- Under $2.2M
  isForeignCorp := false
  isDomesticCorp := true
  isInsuranceCompany := true
  isQualifiedSmallBusiness := true  -- KEY: Is insurance a "qualified trade"?
  isTrust := false
  isGrantorTrust := false
  yearsHeld := 6
}

#eval s!"=== SCENARIO 1: Captive + QSBS ==="
#eval s!"§831(b) qualified: {qualifiesFor831b captiveQSBS}"
#eval s!"§1202 QSBS qualified: {qualifiesForQSBS captiveQSBS}"
#eval s!"Benefit score: {benefitScore captiveQSBS}"
#eval s!"ARBITRAGE: {isArbitrage captiveQSBS}"
#eval s!"ISSUE: Insurance may not be 'qualified trade or business' under §1202(e)(3)"
#eval ""

-- Scenario 2: CFC that avoids BOTH Subpart F AND PFIC
-- Active business CFC with CFC exemption from PFIC
def activeCFC : MultiEntity := {
  name := "Active CFC (No PFIC, No Subpart F)"
  usOwnershipPct := 100/100
  foreignOwnershipPct := 0
  totalIncome := 10000000
  passiveIncomePct := 20/100  -- Under 75% = no PFIC
  activeBusinessIncomePct := 80/100  -- Active = no Subpart F
  underwritingIncome := 0
  investmentIncome := 2000000
  totalAssets := 100000000
  passiveAssetsPct := 30/100  -- Under 50% = no PFIC asset test
  qbai := 80000000  -- High QBAI = low GILTI
  insurancePremiums := 0
  isForeignCorp := true
  isDomesticCorp := false
  isInsuranceCompany := false
  isQualifiedSmallBusiness := false
  isTrust := false
  isGrantorTrust := false
  yearsHeld := 10
}

#eval s!"=== SCENARIO 2: Active CFC ==="
#eval s!"Is CFC: {isCFC activeCFC}"
#eval s!"Is PFIC: {isPFIC activeCFC}"
#eval s!"CFC exempt from PFIC: {isCFCExemptFromPFIC activeCFC}"
#eval s!"GILTI reduction (10% QBAI): ${giltiReduction activeCFC}"
#eval s!"Benefit score: {benefitScore activeCFC}"
#eval s!"RESULT: Active income deferred, no PFIC, GILTI reduced by $8M"
#eval ""

-- Scenario 3: IDGT that owns CFC
-- Grantor trust benefits + CFC deferral
def idgtOwnsCFC : MultiEntity := {
  name := "IDGT owns CFC"
  usOwnershipPct := 100/100  -- IDGT is US person for this
  foreignOwnershipPct := 0
  totalIncome := 5000000
  passiveIncomePct := 30/100
  activeBusinessIncomePct := 70/100
  underwritingIncome := 0
  investmentIncome := 1500000
  totalAssets := 50000000
  passiveAssetsPct := 25/100
  qbai := 40000000
  insurancePremiums := 0
  isForeignCorp := true
  isDomesticCorp := false
  isInsuranceCompany := false
  isQualifiedSmallBusiness := false
  isTrust := true
  isGrantorTrust := true
  yearsHeld := 5
}

#eval s!"=== SCENARIO 3: IDGT owns CFC ==="
#eval s!"Is Grantor Trust: {isGrantorTrustQualified idgtOwnsCFC}"
#eval s!"CFC status: {isCFC idgtOwnsCFC}"
#eval s!"PFIC status: {isPFIC idgtOwnsCFC}"
#eval s!"Benefit score: {benefitScore idgtOwnsCFC}"
#eval s!"COMPLEXITY: Who is the 'US shareholder' - grantor or trust?"
#eval ""

-- Scenario 4: The 74% PFIC Edge Case
-- Just under 75% passive income - NOT a PFIC
def pficEdge : MultiEntity := {
  name := "74% Passive - NOT PFIC"
  usOwnershipPct := 100/100
  foreignOwnershipPct := 0
  totalIncome := 1000000
  passiveIncomePct := 74/100  -- Just under!
  activeBusinessIncomePct := 26/100
  underwritingIncome := 0
  investmentIncome := 740000
  totalAssets := 10000000
  passiveAssetsPct := 49/100  -- Just under!
  qbai := 0
  insurancePremiums := 0
  isForeignCorp := true
  isDomesticCorp := false
  isInsuranceCompany := false
  isQualifiedSmallBusiness := false
  isTrust := false
  isGrantorTrust := false
  yearsHeld := 3
}

#eval s!"=== SCENARIO 4: PFIC Edge (74% Passive) ==="
#eval s!"Passive income: 74%"
#eval s!"Is PFIC: {isPFIC pficEdge}"
#eval s!"Is CFC: {isCFC pficEdge}"
#eval s!"CFC but NOT PFIC: {isCFC pficEdge && !isPFIC pficEdge}"
#eval s!"RESULT: CFC treatment (better than PFIC) despite mostly passive"
#eval ""

-- Scenario 5: QSBS inside Opportunity Zone? (§1400Z + §1202)
-- Double exclusion potential?
def qsbsInQOZ : MultiEntity := {
  name := "QSBS in Opportunity Zone"
  usOwnershipPct := 100/100
  foreignOwnershipPct := 0
  totalIncome := 500000
  passiveIncomePct := 5/100
  activeBusinessIncomePct := 95/100
  underwritingIncome := 0
  investmentIncome := 25000
  totalAssets := 30000000
  passiveAssetsPct := 10/100
  qbai := 0
  insurancePremiums := 0
  isForeignCorp := false
  isDomesticCorp := true
  isInsuranceCompany := false
  isQualifiedSmallBusiness := true
  isTrust := false
  isGrantorTrust := false
  yearsHeld := 10
}

#eval s!"=== SCENARIO 5: QSBS + Opportunity Zone ==="
#eval s!"QSBS qualified: {qualifiesForQSBS qsbsInQOZ}"
#eval s!"If in QOZ: Could exclude gain TWICE?"
#eval s!"  - §1202: Exclude $10M gain from QSBS"
#eval s!"  - §1400Z-2: Exclude appreciation after 10 years"
#eval s!"RESEARCH NEEDED: Do the exclusions stack or overlap?"
#eval ""

/-!
## SUMMARY: Best Arbitrage Opportunities
-/

#eval s!"=========================================="
#eval s!"CROSS-SECTION ARBITRAGE FINDINGS"
#eval s!"=========================================="
#eval s!""
#eval s!"1. CFC at 74% passive - Gets CFC treatment (deferral)"
#eval s!"   instead of PFIC (punitive). Just stay under 75%."
#eval s!""
#eval s!"2. CFC with high QBAI - $80M tangible assets = $8M"
#eval s!"   excluded from GILTI. Put factories in CFC."
#eval s!""
#eval s!"3. IDGT + CFC - Grantor pays US tax, but CFC defers"
#eval s!"   foreign income. Complex attribution issues."
#eval s!""
#eval s!"4. QSBS + QOZ - Potential double exclusion?"
#eval s!"   §1202 excludes $10M, §1400Z excludes appreciation."
#eval s!"   Need to verify stacking."
#eval s!""
#eval s!"5. Captive + QSBS - Probably doesn't work."
#eval s!"   Insurance not a 'qualified trade' under §1202(e)(3)."

end
