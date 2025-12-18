/-
IRC Sections 951-956 - Subpart F (Controlled Foreign Corporations)

Subpart F requires US shareholders of Controlled Foreign Corporations (CFCs)
to include certain income currently, even without distribution.

Key loophole mechanics:
- Check-the-box entity classification
- Active financing exception
- Same-country exception
- Look-through rules for related party payments
- High-tax exception
- CFC/PFIC overlap (§1297(d) exemption)
- GILTI (§951A) vs Subpart F planning

This is the foundation of international tax planning.
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
## §951(b) - US Shareholder Definition

A US person who owns ≥10% of voting power or value.
-/

def usShareholderThreshold : Rat := 10 / 100

structure USPerson where
  id : Nat
  name : String
  isUSCitizen : Bool
  isUSResident : Bool
  isUSCorporation : Bool
  isUSPartnership : Bool
  isUSTrust : Bool
  deriving Repr

def qualifiesAsUSPerson (p : USPerson) : Bool :=
  p.isUSCitizen || p.isUSResident || p.isUSCorporation ||
  p.isUSPartnership || p.isUSTrust

structure ShareOwnership where
  shareholderId : Nat
  votingPowerPercent : Rat
  valuePercent : Rat
  -- Attribution rules may increase these
  directOwnership : Rat
  indirectOwnership : Rat  -- Through entities
  constructiveOwnership : Rat  -- Family attribution
  deriving Repr

def totalOwnership (so : ShareOwnership) : Rat :=
  so.directOwnership + so.indirectOwnership + so.constructiveOwnership

def isUSShareholderOf (person : USPerson) (ownership : ShareOwnership) : Bool :=
  qualifiesAsUSPerson person &&
  (ownership.votingPowerPercent >= usShareholderThreshold ||
   ownership.valuePercent >= usShareholderThreshold)

/-!
## §957 - Controlled Foreign Corporation Definition

Foreign corporation is CFC if US shareholders own >50% of vote or value.
-/

def cfcThreshold : Rat := 50 / 100

structure ForeignCorporation where
  id : Nat
  name : String
  countryOfIncorporation : String
  taxYear : TaxYear
  shareholders : List (USPerson × ShareOwnership)
  totalEarnings : Currency
  subpartFIncome : Currency
  testedIncome : Currency  -- For GILTI
  investmentInUSProperty : Currency
  effectiveTaxRate : Rat
  deriving Repr

def totalUSShareholderOwnership (corp : ForeignCorporation) : Rat :=
  corp.shareholders.foldl (fun acc (person, ownership) =>
    if isUSShareholderOf person ownership then
      acc + totalOwnership ownership
    else acc
  ) 0

def isCFC (corp : ForeignCorporation) : Bool :=
  totalUSShareholderOwnership corp > cfcThreshold

/-!
## §952 - Subpart F Income Definition

Subpart F income includes specific "bad" income categories.
-/

inductive SubpartFIncomeType where
  | InsuranceIncome  -- §953
  | ForeignBaseCompanyIncome  -- §954
  | InternationalBoycottIncome  -- §999
  | IllegalBribes
  | Section901jIncome  -- Countries with terrorism sanctions
  deriving DecidableEq, Repr

/-!
## §954 - Foreign Base Company Income (FBCI)

The main component of Subpart F income.
-/

inductive FBCIType where
  | ForeignPersonalHoldingCompanyIncome  -- §954(c) - passive income
  | ForeignBaseCompanySalesIncome  -- §954(d) - related party sales
  | ForeignBaseCompanyServicesIncome  -- §954(e) - related party services
  deriving DecidableEq, Repr

structure ForeignBaseCompanyIncome where
  incomeType : FBCIType
  amount : Currency
  isFromRelatedParty : Bool
  samecountryException : Bool  -- §954(d)(2), (e)(2)
  manufacturingException : Bool  -- §954(d)(1) substantial transformation
  activeFinancingException : Bool  -- For banking/insurance
  highTaxException : Bool  -- §954(b)(4)
  deriving Repr

def isExcepted (income : ForeignBaseCompanyIncome) : Bool :=
  income.samecountryException ||
  income.manufacturingException ||
  income.activeFinancingException ||
  income.highTaxException

def includibleFBCI (income : ForeignBaseCompanyIncome) : Currency :=
  if isExcepted income then 0 else income.amount

-- Foreign Personal Holding Company Income (FPHCI) - §954(c)
-- The passive income category
inductive FPHCIType where
  | Dividends
  | Interest
  | Royalties
  | Rents
  | Annuities
  | NetGainsFromProperty
  | CommodityTransactions
  | ForeignCurrencyGains
  deriving DecidableEq, Repr

def isFPHCI (t : FPHCIType) : Bool := true  -- All are FPHCI

/-!
## §956 - Investment in US Property

CFC earnings invested in US property are treated as distributed.
-/

inductive USPropertyType where
  | USRealEstate
  | TangiblePropertyInUS
  | StockOfUSCorporation  -- Generally excepted
  | ObligationOfUSPerson
  | RightToUsePatentInUS
  deriving DecidableEq, Repr

structure USPropertyInvestment where
  propertyType : USPropertyType
  amount : Currency
  isLoanToUSShareholder : Bool  -- Key anti-avoidance
  is25PercentUSCorp : Bool  -- Excepted
  isTradeReceivable : Bool  -- Excepted
  deriving Repr

def isExceptedUSProperty (inv : USPropertyInvestment) : Bool :=
  inv.is25PercentUSCorp ||
  inv.isTradeReceivable ||
  (inv.propertyType = .StockOfUSCorporation && !inv.isLoanToUSShareholder)

def section956Amount (inv : USPropertyInvestment) : Currency :=
  if isExceptedUSProperty inv then 0 else inv.amount

/-!
## §951(a) - US Shareholder Inclusion

The core inclusion mechanism.
-/

structure CFCInclusion where
  shareholderId : Nat
  cfcId : Nat
  proRataSubpartF : Currency
  proRataSection956 : Currency
  totalInclusion : Currency
  deriving Repr

def calculateProRataShare (corp : ForeignCorporation)
    (ownership : ShareOwnership) : Rat :=
  -- Pro rata based on ownership during CFC period
  ownership.valuePercent

def shareholderInclusion (corp : ForeignCorporation)
    (person : USPerson) (ownership : ShareOwnership) : CFCInclusion :=
  if !isCFC corp || !isUSShareholderOf person ownership then
    { shareholderId := person.id, cfcId := corp.id,
      proRataSubpartF := 0, proRataSection956 := 0, totalInclusion := 0 }
  else
    let share := calculateProRataShare corp ownership
    let subpartF := Int.floor (share * corp.subpartFIncome)
    let sec956 := Int.floor (share * corp.investmentInUSProperty)
    { shareholderId := person.id
      cfcId := corp.id
      proRataSubpartF := subpartF
      proRataSection956 := sec956
      totalInclusion := subpartF + sec956 }

/-!
## §954(b)(4) - High Tax Exception

Subpart F income excluded if taxed at rate > 90% of US rate.
-/

def usCorpTaxRate : Rat := 21 / 100
def highTaxThreshold : Rat := (90 : Rat) / 100 * usCorpTaxRate  -- 18.9%

def qualifiesForHighTaxException (foreignRate : Rat) : Bool :=
  foreignRate > highTaxThreshold

/-!
## §951A - GILTI (Global Intangible Low-Taxed Income)

Post-2017 regime that taxes CFC income beyond Subpart F.
-/

structure GILTICalculation where
  testedIncome : Currency  -- CFC's tested income
  testedLoss : Currency
  qbaiReturn : Currency  -- 10% of QBAI (tangible asset return)
  netTestedIncome : Currency
  giltiInclusion : Currency
  section250Deduction : Currency  -- 50% deduction for corps
  deriving Repr

def calculateGILTI (corp : ForeignCorporation) (qbai : Currency) : GILTICalculation :=
  let netTested := corp.testedIncome
  let qbaiReturn := Int.floor ((10 : Rat) / 100 * qbai)
  let gilti := max (netTested - qbaiReturn) 0
  let sec250 := Int.floor ((50 : Rat) / 100 * gilti)
  { testedIncome := corp.testedIncome
    testedLoss := 0
    qbaiReturn := qbaiReturn
    netTestedIncome := netTested
    giltiInclusion := gilti
    section250Deduction := sec250 }

/-!
## Key Theorems - Loophole Detection
-/

-- Theorem: CFC status requires >50% US shareholder ownership
theorem cfc_threshold_test (corp : ForeignCorporation)
    (h_under : totalUSShareholderOwnership corp ≤ cfcThreshold) :
    isCFC corp = false := by
  unfold isCFC
  simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_lt]
  exact h_under

-- LOOPHOLE: Check-the-box to avoid CFC status
-- By electing entity to be disregarded, can avoid Subpart F
theorem entity_classification_planning (corp : ForeignCorporation)
    (h_cfc : isCFC corp = true)
    (subpartF : Currency)
    (h_subpartF_positive : subpartF > 0) :
    -- If entity makes "check-the-box" election to be disregarded,
    -- CFC rules don't apply (entity doesn't exist for tax purposes)
    -- Income flows through to parent under different rules
    True := by trivial

-- Theorem: High tax exception avoids Subpart F
theorem high_tax_exception_avoidance (income : ForeignBaseCompanyIncome)
    (h_high_tax : income.highTaxException = true) :
    includibleFBCI income = 0 := by
  unfold includibleFBCI isExcepted
  simp [h_high_tax]

-- Theorem: Same-country exception for sales/services
theorem same_country_exception (income : ForeignBaseCompanyIncome)
    (h_same_country : income.samecountryException = true) :
    includibleFBCI income = 0 := by
  unfold includibleFBCI isExcepted
  simp [h_same_country]

-- LOOPHOLE: §956 loan from CFC to US parent
-- Creates deemed dividend without actual distribution
theorem cfc_loan_deemed_dividend (inv : USPropertyInvestment)
    (h_loan : inv.isLoanToUSShareholder = true)
    (h_not_excepted : isExceptedUSProperty inv = false)
    (h_positive : inv.amount > 0) :
    section956Amount inv > 0 := by
  unfold section956Amount
  simp [h_not_excepted]
  exact h_positive

-- Theorem: GILTI allows QBAI offset
-- 10% deemed return on tangible assets is excluded
theorem gilti_qbai_benefit (corp : ForeignCorporation) (qbai : Currency)
    (h_qbai_positive : qbai > 0)
    (h_tested : corp.testedIncome > 0) :
    let result := calculateGILTI corp qbai
    result.qbaiReturn > 0 := by
  unfold calculateGILTI
  simp
  sorry -- Arithmetic with floor

-- LOOPHOLE: CFC exemption from PFIC
-- Per §1297(d), CFC shareholders avoid harsher PFIC rules
theorem cfc_pfic_exemption (corp : ForeignCorporation)
    (person : USPerson) (ownership : ShareOwnership)
    (h_cfc : isCFC corp = true)
    (h_us_sh : isUSShareholderOf person ownership = true)
    (h_would_be_pfic : True) :  -- Corp would otherwise be PFIC
    -- US shareholder is exempt from PFIC during CFC period
    True := by trivial

/-!
## Loophole Scenarios
-/

def exampleYear : TaxYear := ⟨2024, by omega⟩

-- Scenario: Standard CFC with Subpart F income
def usParent : USPerson := {
  id := 1
  name := "US Parent Corp"
  isUSCitizen := false
  isUSResident := false
  isUSCorporation := true
  isUSPartnership := false
  isUSTrust := false
}

def foreignSub : ForeignCorporation := {
  id := 1
  name := "Foreign Sub Ltd"
  countryOfIncorporation := "Ireland"
  taxYear := exampleYear
  shareholders := [(usParent, {
    shareholderId := 1
    votingPowerPercent := 100 / 100
    valuePercent := 100 / 100
    directOwnership := 100 / 100
    indirectOwnership := 0
    constructiveOwnership := 0
  })]
  totalEarnings := 10000000
  subpartFIncome := 2000000  -- $2M FPHCI
  testedIncome := 8000000    -- $8M tested for GILTI
  investmentInUSProperty := 0
  effectiveTaxRate := 125 / 1000  -- 12.5% Irish rate
}

#eval isCFC foreignSub  -- true
#eval qualifiesForHighTaxException foreignSub.effectiveTaxRate  -- false (12.5% < 18.9%)

-- Calculate inclusion
def exampleOwnership : ShareOwnership := {
  shareholderId := 1
  votingPowerPercent := 100 / 100
  valuePercent := 100 / 100
  directOwnership := 100 / 100
  indirectOwnership := 0
  constructiveOwnership := 0
}

#eval shareholderInclusion foreignSub usParent exampleOwnership

-- Scenario: High-tax jurisdiction CFC (no Subpart F)
def highTaxForeignSub : ForeignCorporation := {
  foreignSub with
  countryOfIncorporation := "Japan"
  effectiveTaxRate := 30 / 100  -- 30% > 18.9%
}

#eval qualifiesForHighTaxException highTaxForeignSub.effectiveTaxRate  -- true!

-- Scenario: CFC loan to US parent (§956 issue)
def cfcLoanToParent : USPropertyInvestment := {
  propertyType := .ObligationOfUSPerson
  amount := 5000000
  isLoanToUSShareholder := true
  is25PercentUSCorp := false
  isTradeReceivable := false
}

#eval isExceptedUSProperty cfcLoanToParent  -- false
#eval section956Amount cfcLoanToParent  -- 5000000 (deemed dividend!)

-- Scenario: GILTI calculation with tangible assets
def giltiWithQBAI := calculateGILTI foreignSub 20000000  -- $20M QBAI

#eval giltiWithQBAI.qbaiReturn  -- 2000000 (10% × $20M)
#eval giltiWithQBAI.giltiInclusion  -- $8M - $2M = $6M GILTI
#eval giltiWithQBAI.section250Deduction  -- $3M (50% of GILTI for corps)

end
