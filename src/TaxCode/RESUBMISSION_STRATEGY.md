# RESUBMISSION STRATEGY FOR 6 CRITICAL SECTIONS
**Generated**: 2025-12-12
**Analysis**: Grok-4 ultrathink review
**Sections**: 151, 152, 401, 1001, 1012, 1221

---

## EXECUTIVE SUMMARY

**Current State**:
- ✅ 2 sections fixed: Section 1, Section 71 (now COMPLETE)
- ❌ 6 sections remain CRITICAL (scored 1-3/10)
- 🎯 All 6 analyzed with Grok-4 for resubmission

**Root Cause Analysis**:
1. **Compile Failures** (151, 152): `#check placeholder` - undefined identifier
2. **TODOs Only** (1001, 1012, 1221): No implementation, just legal text
3. **Partial Implementation** (401): ~40% complete, missing qualification requirements

---

## SECTION-BY-SECTION RESUBMISSION PLANS

### 1. Section 151 - Personal Exemptions (CRITICAL: Score 1/10)

**Current Issue**: `#check placeholder` - undefined identifier causes compilation failure

**Grok-4 Analysis**:
- **Root Cause**: placeholder stub left unresolved in TODO section
- **Core Logic**: Personal exemptions = $0 for 2018-2025 (TCJA), NEW seniors deduction $6,000 for age 65+ (2025-2029) with MAGI phaseout

**Minimal Structures Needed**:
1. `FilingStatus` - Enum (Single, Joint)
2. `Taxpayer` - age: Nat, MAGI: Nat (dollars)
3. `DeductionParams` - base: $6,000, thresholds: $75K/$150K, rate: 6%
4. `PhaseoutResult` - reduction: Nat, finalDeduction: Nat

**Minimal Functions Needed**:
1. `isSenior: Taxpayer → Bool` - checks age ≥ 65
2. `computePhaseout: Nat → FilingStatus → Nat` - calculates 6% * (MAGI - threshold)
3. `seniorDeduction: Taxpayer → TaxYear → Nat` - applies phaseout, handles year ranges
4. `totalDeduction: List Taxpayer → TaxYear → Nat` - sums for all qualifying taxpayers

**Enhanced Resubmission Prompt** (78 words):
```
Formalize IRC §151 in Lean 4: Define structures for FilingStatus (Single/Joint),
Taxpayer (age, MAGI), and params (senior deduction $6K for 65+, phaseouts $75K/$150K
at 6%/dollar). Implement functions: isSenior, computePhaseout (excess MAGI * 0.06),
seniorDeduction (max(0, 6000 - phaseout) for 2025-2029; $0 exemptions 2018-2025).
Ensure year-specific logic. Prove properties like phaseout monotonicity. Replace TODOs;
end with theorem checks, no placeholders. Output complete, compilable Lean file.
```

---

### 2. Section 152 - Dependent Defined (CRITICAL: Score 1/10)

**Current Issue**: `#check placeholder` - undefined identifier causes compilation failure

**Grok-4 Analysis**:
- **Root Cause**: Unresolved dependency validation stub
- **Core Logic**: Qualifying child (relationship, residency, age, support) vs. qualifying relative (relationship, income < exemption, support >50%)
- **Critical**: Used by §21, §24, §32, §151

**Minimal Structures Needed**:
1. `QualifyingChild` - relationshipType, residencyMonths, age, selfSupportPct
2. `QualifyingRelative` - relationshipType, grossIncome, supportProvidedPct
3. `DependentTestResult` - isQualifying: Bool, failureReasons: List String
4. `SectionReference` - linkedSections for §21/§24/§32/§151 cross-refs

**Minimal Functions Needed**:
1. `validateQualifyingChild: PersonData → DependentTestResult` - applies all tests
2. `checkRelationship: String → Int → Bool` - validates relationship type
3. `checkSupportThreshold: Float → Float → Bool` - support >= threshold
4. `resolveDependencies: Array → ValidationError[]` - fixes placeholder refs

**Enhanced Resubmission Prompt** (72 words):
```
Replace "#check placeholder" with concrete dependency resolver for §21/§24/§32/§151.
Implement QualifyingChild (relationship, residency>6mo, age<19 or student<24, support<50%)
and QualifyingRelative (relationship, income<exemption, support>50%). Test with sample:
17-year-old child, 6-month residency, <50% self-support. Ensure compilation passes and
outputs qualifying status. Resubmit with error logs for review.
```

---

### 3. Section 401 - Qualified Pension Plans (CRITICAL: Score 3/10)

**Current State**: HAS coverage/nondiscrimination logic but MISSING:
- §401(a)(1)-(36) qualification requirements (only has 3, 4, 26)
- Vesting rules
- Distribution rules
- Contribution limits

**Grok-4 Analysis - 5 Key Qualification Requirements to Add**:

1. **§401(a)(1) - Domestic Trust**: Mandate trust created/organized in U.S., irrevocable
2. **§401(a)(2) - Exclusive Benefit**: Trust for exclusive benefit of employees, no employer reversion
3. **§401(a)(7) - Nonforfeitable Rights**: Full vesting by plan termination or discontinuation
4. **§401(a)(9) - Required Minimum Distributions (RMDs)**: Distributions must begin by age 73 (post-SECURE 2.0)
5. **§401(a)(11) - Qualified Joint and Survivor Annuity (QJSA)**: Default form for married participants

**Structures/Functions for Vesting**:
- Structure: `VestingSchedule` - yearsOfService: Nat, vestedPercentage: Nat (0-100), isCliffVesting: Bool
- Function: `calculateVestedBalance: VestingSchedule → YearsOfService → AccountBalance → Currency`
- Rule: Min 100% vesting at 3 years (cliff) or 20%/year over 6 years (graded) per §401(a)(7)

**Enhanced Resubmission Prompt** (100 words):
```
Extend IRC §401 formalization: Add 5 critical qualification requirements: (1) domestic trust
(§401(a)(1)), (2) exclusive benefit (§401(a)(2)), (7) vesting by termination, (9) RMDs at 73,
(11) QJSA for married. Implement VestingSchedule structure with calculateVestedBalance function
(3-year cliff or 6-year graded). Model contribution limits: $22,500 (2023) with $7,500 catch-up
for 50+. Add Plan.contributionLimit and Plan.vestingSchedule fields. Prove theorems: vested <=
account balance, RMD age >= 73. Keep existing coverage/nondiscrimination. Output complete Lean file.
```

---

### 4. Section 1001 - Gain/Loss Determination (CRITICAL: Score 2/10)

**Current Issue**: Only TODOs and `#eval "Section loaded"` - no implementation

**Grok-4 Analysis**:
- **Core Logic**: Gain = Amount Realized - Adjusted Basis; Loss = Adjusted Basis - Amount Realized
- **§1001(a)**: Compute gain/loss from sale/exchange
- **§1001(b)**: Amount realized = money + FMV of property - real property tax adjustments
- **§1001(c)**: Entire gain/loss recognized except as otherwise provided

**Structures Needed** (4):
1. `AdjustedBasis` - originalCost, additions (improvements), subtractions (depreciation)
2. `AmountRealized` - money: Currency, fmvProperty: Currency, taxAdjustments: Currency
3. `GainLossResult` - value: Currency, isGain: Bool, isRecognized: Bool
4. `TransactionDetails` - propertyType, buyerAssumptions

**Functions Needed** (4):
1. `computeAdjustedBasis: Currency → List Currency → List Currency → Currency` - original + additions - subtractions
2. `computeAmountRealized: Currency → Currency → Currency → Currency` - money + FMV - taxes
3. `computeGainLoss: Currency → Currency → GainLossResult` - returns gain (positive) or loss (negative)
4. `determineRecognition: GainLossResult → List Exception → Bool` - checks for §§1031/1033 non-recognition

**Enhanced Resubmission Prompt** (72 words):
```
Formalize IRC §1001 with structures: AdjustedBasis (cost, additions, subtractions),
AmountRealized (money, FMV, taxes), GainLossResult (value, isGain, isRecognized).
Implement computeGainLoss (amount realized - adjusted basis). Include cross-refs to
§1011 (basis) and §§1031/1033 (non-recognition). Example: property sold $200K, basis
$150K = $50K gain. Handle zero gain and losses explicitly. Output complete Lean file.
```

---

### 5. Section 1012 - Cost Basis (CRITICAL: Score 2/10)

**Current Issue**: Only TODOs and `#eval "Section loaded"` - no implementation

**Grok-4 Analysis**:
- **Core**: Basis = cost of property (except subchapters C/K/P)
- **§1012(a)**: General rule - basis = cost
- **§1012(b)**: Exclude apportioned real estate taxes
- **§1012(c)-(d)**: Account-by-account for securities, dividend reinvestment

**Structures Needed** (4):
1. `Property` - type: PropertyType, acquisitionDate, costBasis: Currency
2. `RealEstateTaxes` - sellerPaid: Currency, buyerPaid: Currency, apportioned: Currency
3. `SecurityAccount` - shares: Nat, acquisitionDates: List Date, costPerShare: Currency
4. `DividendReinvestment` - reinvestedAmount: Currency, sharesPurchased: Nat

**Functions Needed** (4):
1. `computeCostBasis: Property → Currency` - returns cost (default rule)
2. `adjustForRealEstateTaxes: Currency → RealEstateTaxes → Currency` - cost - apportioned taxes
3. `accountByAccountBasis: List SecurityAccount → Currency` - tracks by account (§1012(c))
4. `dividendReinvestmentBasis: DividendReinvestment → Currency` - average basis method (§1012(d))

**Enhanced Resubmission Prompt** (80 words):
```
Formalize IRC §1012 with structures: Property (type, date, cost), RealEstateTaxes,
SecurityAccount, DividendReinvestment. Implement computeCostBasis (default = cost),
adjustForRealEstateTaxes (cost - apportioned), accountByAccount (§1012(c)),
dividendReinvestmentBasis (average method §1012(d)). Cross-ref subchapters C/K/P for
exceptions. Example: property cost $100K, seller taxes $2K apportioned = basis $98K.
Output complete Lean file.
```

---

### 6. Section 1221 - Capital Asset Defined (CRITICAL: Score 2/10)

**Current Issue**: Only TODOs and `#eval "Section loaded"` - no implementation

**Grok-4 Analysis**:
- **Core**: Capital asset = property EXCEPT 8 exclusions in §1221(a)
- **Critical**: Determines capital vs ordinary treatment (affects tax rates significantly)

**§1221(a) Exclusions** (8):
1. Inventory/stock in trade
2. Depreciable/real property used in business
3. Copyrights/patents by creator
4. Accounts receivable
5. Government publications
6. Commodities derivatives (dealers)
7. Hedging transactions
8. Supplies regularly consumed

**Structures Needed** (4):
1. `PropertyType` - Enum with 9 types (Capital + 8 exclusions)
2. `Property` - type: PropertyType, heldInBusiness: Bool, createdByTaxpayer: Bool
3. `CapitalAssetTest` - isCapitalAsset: Bool, exclusionReason: Option String
4. `Transaction` - property: Property, saleDate, purpose

**Functions Needed** (4):
1. `isInventory: Property → Bool` - stock in trade test
2. `isDepreciableProperty: Property → Bool` - used in business + subject to §167
3. `isCapitalAsset: Property → CapitalAssetTest` - applies all 8 exclusion tests
4. `determineCharacter: Transaction → CharacterType` - Capital vs Ordinary

**Enhanced Resubmission Prompt** (80 words):
```
Formalize IRC §1221 with PropertyType enum (Capital + 8 exclusions), Property structure,
CapitalAssetTest result. Implement isInventory, isDepreciableProperty, isCapitalAsset
(applies 8 tests), determineCharacter. §1221(a) exclusions: (1) inventory, (2) depreciables,
(3) self-created IP, (4) receivables, (5) govt pubs, (6) commodities, (7) hedging, (8)
supplies. Example: rental property = capital asset, inventory = ordinary. Output complete
Lean file.
```

---

## IMPLEMENTATION PRIORITY

**Immediate Resubmissions** (highest impact):
1. **Section 152** - Blocks §21, §24, §32, §151 (most dependencies)
2. **Section 1001** - Foundation for all capital gains calculations
3. **Section 1221** - Determines capital vs ordinary treatment

**Secondary Resubmissions**:
4. **Section 151** - Seniors deduction (new 2025 provision)
5. **Section 1012** - Cost basis (complements §1001)

**Enhancement** (not full rerun):
6. **Section 401** - Extend existing partial implementation with 5 key requirements

---

## SUCCESS METRICS

**For each resubmission, ensure**:
✅ Passes Lean 4 compilation (no syntax errors)
✅ No `placeholder` or undefined identifiers
✅ At least 3-5 structures and 3-5 functions implemented
✅ At least 2 proven theorems (no 'sorry')
✅ At least 1 working `#eval` example
✅ Score improvement: CRITICAL → MODERATE (4-6) or GOOD (7-8)

---

## NEXT STEPS

1. **Create GitHub issues** for each of the 6 sections with Grok analysis attached
2. **Resubmit to Aristotle** using enhanced prompts above
3. **Monitor completion** via aristotle_queue.json
4. **Re-audit** using audit script after completion
5. **Update README** with new statistics

**Expected Outcome**: 6 CRITICAL → 0 CRITICAL, bringing production-ready count from 15 (60%) to 21 (84%)

---

## APPENDIX: GROK-4 FULL ANALYSIS

<details>
<summary>Section 151 Full Analysis</summary>

### 1. Root Cause of `placeholder` Error
The error stems from `#check placeholder` referencing an undefined identifier. `placeholder` is likely a TODO stub left unresolved, causing Lean 4's compiler to fail name resolution. Remove or define it to fix.

### 2. Minimal Structures Needed (3-5)
- `FilingStatus`: Enum (Single, Joint).
- `Taxpayer`: Structure with age (Nat), MAGI (Nat in dollars).
- `DeductionParams`: Structure holding base senior deduction ($6,000), phaseout thresholds ($75K Single, $150K Joint), and rate (6% per dollar).
- `PhaseoutResult`: Structure for computed reduction and final deduction.

### 3. Minimal Functions Needed (3-5)
- `isSenior`: Bool function checking if age ≥ 65.
- `computePhaseout`: Nat function calculating reduction (6% of excess MAGI over threshold).
- `seniorDeduction`: Nat function applying phaseout to $6,000 base (zero for non-seniors; $0 exemptions per TCJA).
- `totalDeduction`: Nat function summing for tax year (handling 2018-2029 rules).

### 4. Enhanced Aristotle Resubmission Prompt (78 words)
Formalize IRC §151 in Lean 4: Define structures for FilingStatus (Single/Joint), Taxpayer (age, MAGI), and params (senior deduction $6K for 65+, phaseouts $75K/$150K at 6%/dollar). Implement functions: isSenior, computePhaseout (excess MAGI * 0.06), seniorDeduction (max(0, 6000 - phaseout) for 2025-2029; $0 exemptions 2018-2025). Ensure year-specific logic. Prove properties like phaseout monotonicity. Replace TODOs; end with theorem checks, no placeholders. Output complete, compilable Lean file.

</details>

---

**Document Status**: READY FOR IMPLEMENTATION
**Last Updated**: 2025-12-12 via Grok-4 ultrathink analysis
