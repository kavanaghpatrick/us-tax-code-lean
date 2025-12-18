/-
STANDALONE EDGE CASE TESTS
Tests vacuous truth and threshold boundaries in tax code formalizations.
Run with: lake env lean tests/edge_cases/standalone_tests.lean
-/

import Mathlib

set_option linter.unusedVariables false
noncomputable section

abbrev Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

/-!
## §831 Micro-Captive Insurance - Vacuous Truth Test
-/

structure PolicyHolder where
  id : Nat
  premiumsPaid : Currency
  isRelatedParty : Bool
  deriving DecidableEq, Repr

structure SpecifiedHolder where
  id : Nat
  ownershipPercentage : Rat
  specifiedAssetsPercentage : Rat
  isLinealDescendant : Bool
  isSpouseOfDescendant : Bool
  isNonCitizenSpouse : Bool
  deriving Repr

structure InsuranceCompany where
  id : Nat
  taxYear : TaxYear
  netWrittenPremiums : Currency
  directWrittenPremiums : Currency
  policyHolders : List PolicyHolder
  specifiedHolders : List SpecifiedHolder
  hasElected831b : Bool
  controlledGroupPremiums : Currency
  deriving Repr

def basePremiumThreshold : Currency := 2200000

def inflationAdjustedThreshold (year : TaxYear) : Currency :=
  let baseYear := 2015
  let yearsElapsed := year.year - baseYear
  let inflationFactor : Rat := (102 / 100) ^ yearsElapsed
  let adjusted := Int.floor (inflationFactor * basePremiumThreshold)
  (adjusted / 50000) * 50000

def relevantPremiums (co : InsuranceCompany) : Currency :=
  max co.netWrittenPremiums co.directWrittenPremiums

def totalPremiumsWithControlledGroup (co : InsuranceCompany) : Currency :=
  relevantPremiums co + co.controlledGroupPremiums

def meetsPremiumTest (co : InsuranceCompany) : Bool :=
  totalPremiumsWithControlledGroup co ≤ inflationAdjustedThreshold co.taxYear

def deMinimisPercentage : Rat := 2 / 100

def policyholderPremiumPercentage (ph : PolicyHolder) (co : InsuranceCompany) : Rat :=
  let total := relevantPremiums co
  if total = 0 then 0 else (ph.premiumsPaid : Rat) / (total : Rat)

def aggregateRelatedPolicyholders (co : InsuranceCompany) : List PolicyHolder :=
  let related := co.policyHolders.filter (·.isRelatedParty)
  let unrelated := co.policyHolders.filter (fun ph => !ph.isRelatedParty)
  let relatedAggregated : PolicyHolder := {
    id := 0
    premiumsPaid := related.foldl (fun acc ph => acc + ph.premiumsPaid) 0
    isRelatedParty := true
  }
  if related.isEmpty then unrelated else relatedAggregated :: unrelated

def meetsNoPolicyholderOver20Test (co : InsuranceCompany) : Bool :=
  let aggregated := aggregateRelatedPolicyholders co
  aggregated.all fun ph =>
    policyholderPremiumPercentage ph co ≤ (20 : Rat) / 100

def isSpecifiedHolder (sh : SpecifiedHolder) : Bool :=
  sh.isLinealDescendant || sh.isSpouseOfDescendant || sh.isNonCitizenSpouse

def meetsSpecifiedHolderTest (co : InsuranceCompany) : Bool :=
  co.specifiedHolders.all fun sh =>
    if isSpecifiedHolder sh then
      sh.ownershipPercentage ≤ sh.specifiedAssetsPercentage + deMinimisPercentage
    else true

def meetsDiversificationTest (co : InsuranceCompany) : Bool :=
  meetsNoPolicyholderOver20Test co || meetsSpecifiedHolderTest co

def qualifiesFor831b (co : InsuranceCompany) : Bool :=
  meetsPremiumTest co &&
  meetsDiversificationTest co &&
  co.hasElected831b

/-!
### TEST: Concentrated ownership with empty specifiedHolders
-/

def concentratedCompany : InsuranceCompany := {
  id := 1
  taxYear := ⟨2024, by omega⟩
  netWrittenPremiums := 1000000
  directWrittenPremiums := 1000000
  policyHolders := [
    -- ONE policyholder has 100% of premiums - FAILS 20% test
    { id := 1, premiumsPaid := 1000000, isRelatedParty := false }
  ]
  specifiedHolders := []  -- EMPTY LIST!
  hasElected831b := true
  controlledGroupPremiums := 0
}

-- Run the tests
#eval! meetsNoPolicyholderOver20Test concentratedCompany
  -- Expected: false (100% > 20%)

#eval! meetsSpecifiedHolderTest concentratedCompany
  -- Expected: true (VACUOUS - empty list)

#eval! meetsDiversificationTest concentratedCompany
  -- Expected: true (false || true = true) <- LOOPHOLE!

#eval! qualifiesFor831b concentratedCompany
  -- Expected: true <- Company qualifies despite 100% concentration!

/-!
### TEST: Empty policyholders list
-/

def emptyPolicyholders : InsuranceCompany := {
  id := 2
  taxYear := ⟨2024, by omega⟩
  netWrittenPremiums := 0
  directWrittenPremiums := 0
  policyHolders := []  -- EMPTY
  specifiedHolders := []
  hasElected831b := true
  controlledGroupPremiums := 0
}

#eval! meetsNoPolicyholderOver20Test emptyPolicyholders
  -- Expected: true (VACUOUS)

#eval! qualifiesFor831b emptyPolicyholders
  -- Expected: true

/-!
## §1297 PFIC - Threshold Boundary Tests
-/

inductive IncomeType where
  | Dividends
  | Interest
  | ActiveBusinessIncome
  | ActiveBankingIncome
  deriving DecidableEq, Repr

structure IncomeItem where
  incomeType : IncomeType
  amount : Currency
  deriving Repr

structure ForeignCorp where
  incomeItems : List IncomeItem
  isCFC : Bool
  hasUSBankingLicense : Bool
  deriving Repr

def passiveIncomeThreshold : Rat := 75 / 100

def isPassiveIncomeType (t : IncomeType) : Bool :=
  match t with
  | .Dividends => true
  | .Interest => true
  | .ActiveBusinessIncome => false
  | .ActiveBankingIncome => false

def grossIncome (corp : ForeignCorp) : Currency :=
  corp.incomeItems.foldl (fun acc item => acc + item.amount) 0

def passiveIncome (corp : ForeignCorp) : Currency :=
  corp.incomeItems.foldl (fun acc item =>
    if isPassiveIncomeType item.incomeType then acc + item.amount else acc
  ) 0

def passiveIncomeRatio (corp : ForeignCorp) : Rat :=
  let gross := grossIncome corp
  if gross = 0 then 0 else passiveIncome corp / gross

def isPFIC (corp : ForeignCorp) : Bool :=
  passiveIncomeRatio corp ≥ passiveIncomeThreshold

/-!
### TEST: PFIC threshold boundaries
-/

def pficAt74 : ForeignCorp := {
  incomeItems := [
    { incomeType := .Dividends, amount := 74 },
    { incomeType := .ActiveBusinessIncome, amount := 26 }
  ]
  isCFC := false
  hasUSBankingLicense := false
}

def pficAt75 : ForeignCorp := {
  incomeItems := [
    { incomeType := .Dividends, amount := 75 },
    { incomeType := .ActiveBusinessIncome, amount := 25 }
  ]
  isCFC := false
  hasUSBankingLicense := false
}

def pficAt76 : ForeignCorp := {
  incomeItems := [
    { incomeType := .Dividends, amount := 76 },
    { incomeType := .ActiveBusinessIncome, amount := 24 }
  ]
  isCFC := false
  hasUSBankingLicense := false
}

#eval! passiveIncomeRatio pficAt74  -- 74/100
#eval! passiveIncomeRatio pficAt75  -- 75/100
#eval! passiveIncomeRatio pficAt76  -- 76/100

#eval! isPFIC pficAt74  -- false (74% < 75%)
#eval! isPFIC pficAt75  -- true  (75% >= 75%) <- Cliff!
#eval! isPFIC pficAt76  -- true  (76% >= 75%)

/-!
### TEST: Zero income edge case
-/

def zeroIncome : ForeignCorp := {
  incomeItems := []
  isCFC := false
  hasUSBankingLicense := false
}

#eval! grossIncome zeroIncome       -- 0
#eval! passiveIncomeRatio zeroIncome -- 0 (division guard)
#eval! isPFIC zeroIncome            -- false (0 < 75%)

/-!
## §453 Installment Sale - $5M Threshold
-/

def installmentThreshold : Currency := 5000000

def isLargeInstallmentSale (sellingPrice : Currency) : Bool :=
  sellingPrice > installmentThreshold

#eval! isLargeInstallmentSale 4999999  -- false ($1 under)
#eval! isLargeInstallmentSale 5000000  -- false (at threshold, > not >=)
#eval! isLargeInstallmentSale 5000001  -- true  ($1 over triggers!)

/-!
## §951A High-Tax Exception - 18.9% Threshold
-/

def usCorpTaxRate : Rat := 21 / 100
def highTaxThreshold : Rat := (90 : Rat) / 100 * usCorpTaxRate

def qualifiesForHighTaxException (foreignRate : Rat) : Bool :=
  foreignRate > highTaxThreshold

#eval! highTaxThreshold  -- Should be ~18.9%

#eval! qualifiesForHighTaxException (18/100)   -- false
#eval! qualifiesForHighTaxException (189/1000) -- false (exactly 18.9%)
#eval! qualifiesForHighTaxException (19/100)   -- true
#eval! qualifiesForHighTaxException (125/1000) -- false (Ireland 12.5%)
#eval! qualifiesForHighTaxException (30/100)   -- true (Japan 30%)

/-!
## SUMMARY: Key Loopholes Found

1. §831 Vacuous Truth:
   - Empty specifiedHolders list causes meetsSpecifiedHolderTest to return true
   - This bypasses the diversification test even with 100% policyholder concentration

2. §1297 PFIC Threshold Cliff:
   - 74% passive = NOT PFIC
   - 75% passive = PFIC
   - Zero income = 0 ratio = NOT PFIC (division guard)

3. §453 Installment Sale Cliff:
   - $5,000,000 = NO interest charge
   - $5,000,001 = interest charge kicks in

4. §951A High-Tax Exception Cliff:
   - 18.9% foreign tax = NO exception
   - 19% foreign tax = exception applies
-/

end
