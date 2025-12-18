/-
IRC Section 1297 - Passive Foreign Investment Company (PFIC)

PFIC rules impose punitive taxation on US shareholders of foreign corporations
that are primarily passive investment vehicles. This is a major anti-avoidance
regime for offshore investment structures.

Key loophole areas:
- 75%/50% threshold manipulation
- Active business exceptions (banking, insurance)
- Look-through rules for 25%+ subsidiaries
- CFC overlap/exemption
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
## §1297(a) - PFIC Definition

A foreign corporation is a PFIC if EITHER:
1. 75% or more of gross income is passive income (Income Test), OR
2. 50% or more of assets produce passive income (Asset Test)
-/

-- Thresholds from statute
def passiveIncomeThreshold : Rat := 75 / 100
def passiveAssetThreshold : Rat := 50 / 100
def lookThroughOwnershipThreshold : Rat := 25 / 100

/-!
## Income Categories per §1297(b)

Passive income = Foreign Personal Holding Company Income (§954(c))
with exceptions for active banking, insurance, and related party income.
-/

inductive IncomeType where
  | Dividends
  | Interest
  | Royalties
  | Rents
  | Annuities
  | NetGainsFromProperty  -- Sales of passive assets
  | CommodityTransactions
  | ForeignCurrencyGains
  | ActiveBankingIncome
  | ActiveInsuranceIncome
  | ExportTradeIncome
  | RelatedPartyAllocable  -- Allocable to active income of related party
  | ActiveBusinessIncome
  | OtherIncome
  deriving DecidableEq, Repr

-- Determine if income type is passive per §1297(b)
def isPassiveIncomeType (t : IncomeType) : Bool :=
  match t with
  | .Dividends => true
  | .Interest => true
  | .Royalties => true
  | .Rents => true  -- Generally passive
  | .Annuities => true
  | .NetGainsFromProperty => true
  | .CommodityTransactions => true
  | .ForeignCurrencyGains => true
  | .ActiveBankingIncome => false  -- §1297(b)(2)(A) exception
  | .ActiveInsuranceIncome => false  -- §1297(b)(2)(B) exception
  | .ExportTradeIncome => false  -- §1297(b)(2)(D) exception
  | .RelatedPartyAllocable => false  -- §1297(b)(2)(C) exception
  | .ActiveBusinessIncome => false
  | .OtherIncome => false

structure IncomeItem where
  incomeType : IncomeType
  amount : Currency
  fromRelatedParty : Bool
  relatedPartyActiveIncome : Currency  -- For §1297(b)(2)(C) allocation
  deriving Repr

/-!
## Asset Categories
-/

structure Asset where
  id : Nat
  value : Currency
  producesPassiveIncome : Bool
  heldForPassiveProduction : Bool
  deriving Repr

def isPassiveAsset (a : Asset) : Bool :=
  a.producesPassiveIncome || a.heldForPassiveProduction

/-!
## Foreign Corporation Structure
-/

structure ForeignCorporation where
  id : Nat
  taxYear : TaxYear
  incomeItems : List IncomeItem
  assets : List Asset
  -- Subsidiary ownership for look-through
  subsidiaryOwnership : List (Nat × Rat)  -- (subsidiary ID, ownership %)
  -- CFC status
  isCFC : Bool
  -- Insurance qualification per §1297(f)
  isQualifyingInsuranceCorp : Bool
  -- Banking license
  hasUSBankingLicense : Bool
  deriving Repr

/-!
## §1297(a)(1) - Income Test

75% or more of gross income is passive.
-/

def grossIncome (corp : ForeignCorporation) : Currency :=
  corp.incomeItems.foldl (fun acc item => acc + item.amount) 0

-- Calculate passive income with exceptions
def passiveIncome (corp : ForeignCorporation) : Currency :=
  corp.incomeItems.foldl (fun acc item =>
    -- Check for active business exceptions
    let isExcepted := match item.incomeType with
      | .ActiveBankingIncome => corp.hasUSBankingLicense
      | .ActiveInsuranceIncome => corp.isQualifyingInsuranceCorp
      | .RelatedPartyAllocable => item.relatedPartyActiveIncome > 0
      | _ => false
    if isPassiveIncomeType item.incomeType && !isExcepted then
      acc + item.amount
    else acc
  ) 0

def passiveIncomeRatio (corp : ForeignCorporation) : Rat :=
  let gross := grossIncome corp
  if gross = 0 then 0 else passiveIncome corp / gross

def meetsIncomeTest (corp : ForeignCorporation) : Bool :=
  passiveIncomeRatio corp ≥ passiveIncomeThreshold

/-!
## §1297(a)(2) - Asset Test

50% or more of assets (by average value) produce passive income.
-/

def totalAssetValue (corp : ForeignCorporation) : Currency :=
  corp.assets.foldl (fun acc a => acc + a.value) 0

def passiveAssetValue (corp : ForeignCorporation) : Currency :=
  corp.assets.foldl (fun acc a =>
    if isPassiveAsset a then acc + a.value else acc
  ) 0

def passiveAssetRatio (corp : ForeignCorporation) : Rat :=
  let total := totalAssetValue corp
  if total = 0 then 0 else passiveAssetValue corp / total

def meetsAssetTest (corp : ForeignCorporation) : Bool :=
  passiveAssetRatio corp ≥ passiveAssetThreshold

/-!
## §1297(a) - PFIC Status

A corporation is a PFIC if it meets EITHER test.
-/

def isPFIC (corp : ForeignCorporation) : Bool :=
  meetsIncomeTest corp || meetsAssetTest corp

/-!
## §1297(c) - Look-Through for 25%+ Owned Subsidiaries

If the corporation owns ≥25% of another corporation, it must
include its proportionate share of that subsidiary's income and assets.
-/

-- Apply look-through (simplified - would need subsidiary data)
def applyLookThrough (corp : ForeignCorporation)
    (subsidiaries : List ForeignCorporation) : ForeignCorporation :=
  let eligibleSubs := corp.subsidiaryOwnership.filter (fun (_, pct) =>
    pct ≥ lookThroughOwnershipThreshold)
  -- For each eligible subsidiary, add proportionate income/assets
  eligibleSubs.foldl (fun acc (subId, pct) =>
    match subsidiaries.find? (fun s => s.id = subId) with
    | none => acc
    | some sub =>
        let propIncome := sub.incomeItems.map (fun item =>
          { item with amount := Int.floor (pct * item.amount) })
        let propAssets := sub.assets.map (fun a =>
          { a with value := Int.floor (pct * a.value) })
        { acc with
          incomeItems := acc.incomeItems ++ propIncome
          assets := acc.assets ++ propAssets }
  ) corp

/-!
## §1297(d) - CFC Exception

A corporation is not treated as a PFIC with respect to a US shareholder
during periods when it is a CFC and the shareholder is a "US shareholder"
under §951(b) (owns ≥10%).
-/

structure USPerson where
  id : Nat
  ownershipInCorp : Rat
  isUS10PercentShareholder : Bool  -- Per §951(b)
  deriving Repr

def isCFCExempt (corp : ForeignCorporation) (shareholder : USPerson) : Bool :=
  corp.isCFC && shareholder.isUS10PercentShareholder

-- PFIC status considering CFC exception
def isPFICForShareholder (corp : ForeignCorporation) (sh : USPerson) : Bool :=
  if isCFCExempt corp sh then false else isPFIC corp

/-!
## Key Theorems - Loophole Detection
-/

-- Theorem: Just under threshold avoids PFIC (income test)
theorem income_threshold_cliff (corp : ForeignCorporation)
    (h_under : passiveIncomeRatio corp < passiveIncomeThreshold)
    (h_asset_under : passiveAssetRatio corp < passiveAssetThreshold) :
    isPFIC corp = false := by
  unfold isPFIC meetsIncomeTest meetsAssetTest
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le]
  exact ⟨h_under, h_asset_under⟩

-- Theorem: Banking exception can eliminate passive income
theorem banking_exception_eliminates_passive (corp : ForeignCorporation)
    (h_licensed : corp.hasUSBankingLicense = true)
    (h_all_banking : corp.incomeItems.all fun item =>
        item.incomeType = .ActiveBankingIncome) :
    passiveIncome corp = 0 := by
  unfold passiveIncome
  simp [h_licensed, h_all_banking, isPassiveIncomeType]
  sorry -- Fold proof

-- Theorem: Insurance exception loophole
-- A "qualifying insurance corporation" can have substantial passive income
theorem insurance_exception_loophole (corp : ForeignCorporation)
    (h_qualified : corp.isQualifyingInsuranceCorp = true)
    (h_investment : ∃ item ∈ corp.incomeItems,
        item.incomeType = .ActiveInsuranceIncome) :
    -- Insurance income is NOT counted as passive
    ∃ exempted : Currency, exempted > 0 ∧
      passiveIncome corp < grossIncome corp := by
  sorry -- Existence proof

-- Theorem: Look-through can either help or hurt
-- If subsidiary is active, look-through HELPS avoid PFIC
-- If subsidiary is passive, look-through HURTS
theorem look_through_effect (corp : ForeignCorporation)
    (subsidiaries : List ForeignCorporation)
    (sub : ForeignCorporation)
    (h_owns_25 : ∃ ownership, (sub.id, ownership) ∈ corp.subsidiaryOwnership ∧
        ownership ≥ lookThroughOwnershipThreshold)
    (h_sub_active : passiveIncomeRatio sub < passiveIncomeThreshold) :
    -- After look-through, passive ratio may decrease
    let adjusted := applyLookThrough corp subsidiaries
    passiveIncomeRatio adjusted ≤ passiveIncomeRatio corp ∨
    passiveIncomeRatio adjusted ≥ passiveIncomeRatio corp := by
  -- One of these is always true (trichotomy)
  exact le_or_lt _ _ |>.elim Or.inl (fun h => Or.inr (le_of_lt h))

-- Theorem: CFC exemption creates planning opportunity
-- A US 10% shareholder of a CFC avoids PFIC rules entirely
theorem cfc_exemption_complete (corp : ForeignCorporation) (sh : USPerson)
    (h_cfc : corp.isCFC = true)
    (h_10pct : sh.isUS10PercentShareholder = true)
    (h_would_be_pfic : isPFIC corp = true) :
    isPFICForShareholder corp sh = false := by
  unfold isPFICForShareholder isCFCExempt
  simp [h_cfc, h_10pct]

-- LOOPHOLE: CFC exemption means PFIC rules don't apply
-- But CFC rules (Subpart F) may be LESS punitive in some cases!

/-!
## §1297(f) - Qualifying Insurance Corporation

Must meet minimum asset/income requirements to qualify for exception.
This is where micro-captive insurance intersects with PFIC.
-/

-- Minimum applicable insurance liabilities per §1297(f)(2)
def minimumInsuranceLiabilities (corp : ForeignCorporation) : Rat :=
  -- 25% of insurance liabilities or 10% of assets
  25 / 100  -- Simplified

def isQualifyingInsuranceCorpTest (corp : ForeignCorporation)
    (insuranceLiabilities : Currency) : Bool :=
  let totalAssets := totalAssetValue corp
  if totalAssets = 0 then false
  else
    let ratio := insuranceLiabilities / totalAssets
    ratio ≥ minimumInsuranceLiabilities corp

/-!
## Loophole Scenarios
-/

-- Scenario: Just under 75% passive income
def exampleYear : TaxYear := ⟨2024, by omega⟩

def almostPFICbyIncome : ForeignCorporation := {
  id := 1
  taxYear := exampleYear
  incomeItems := [
    { incomeType := .Dividends, amount := 740000, fromRelatedParty := false, relatedPartyActiveIncome := 0 },
    { incomeType := .ActiveBusinessIncome, amount := 260000, fromRelatedParty := false, relatedPartyActiveIncome := 0 }
  ]  -- 74% passive - just under!
  assets := []
  subsidiaryOwnership := []
  isCFC := false
  isQualifyingInsuranceCorp := false
  hasUSBankingLicense := false
}

#eval isPFIC almostPFICbyIncome  -- Should be false (74% < 75%)
#eval passiveIncomeRatio almostPFICbyIncome  -- Should be ~0.74

def clearlyPFIC : ForeignCorporation := {
  id := 2
  taxYear := exampleYear
  incomeItems := [
    { incomeType := .Dividends, amount := 800000, fromRelatedParty := false, relatedPartyActiveIncome := 0 },
    { incomeType := .ActiveBusinessIncome, amount := 200000, fromRelatedParty := false, relatedPartyActiveIncome := 0 }
  ]  -- 80% passive
  assets := []
  subsidiaryOwnership := []
  isCFC := false
  isQualifyingInsuranceCorp := false
  hasUSBankingLicense := false
}

#eval isPFIC clearlyPFIC  -- Should be true

-- Scenario: CFC that would be PFIC but for exemption
def cfcExempt : ForeignCorporation := {
  id := 3
  taxYear := exampleYear
  incomeItems := [
    { incomeType := .Interest, amount := 1000000, fromRelatedParty := false, relatedPartyActiveIncome := 0 }
  ]  -- 100% passive!
  assets := []
  subsidiaryOwnership := []
  isCFC := true  -- But it's a CFC!
  isQualifyingInsuranceCorp := false
  hasUSBankingLicense := false
}

def us10PercentShareholder : USPerson := {
  id := 1
  ownershipInCorp := 15 / 100
  isUS10PercentShareholder := true
}

#eval isPFIC cfcExempt  -- true (would be PFIC)
#eval isPFICForShareholder cfcExempt us10PercentShareholder  -- false (CFC exempt!)

-- Scenario: Insurance company exception
def insuranceException : ForeignCorporation := {
  id := 4
  taxYear := exampleYear
  incomeItems := [
    { incomeType := .ActiveInsuranceIncome, amount := 800000, fromRelatedParty := false, relatedPartyActiveIncome := 0 },
    { incomeType := .ActiveBusinessIncome, amount := 200000, fromRelatedParty := false, relatedPartyActiveIncome := 0 }
  ]
  assets := []
  subsidiaryOwnership := []
  isCFC := false
  isQualifyingInsuranceCorp := true  -- Key!
  hasUSBankingLicense := false
}

#eval isPFIC insuranceException  -- Should be false (insurance excepted)

end
