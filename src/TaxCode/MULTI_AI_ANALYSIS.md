# MULTI-AI ANALYSIS: RESUBMISSION STRATEGY REVIEW
**Date**: 2025-12-12
**Reviewers**: Grok-4, Gemini, Codex CLI (GPT-5)
**Target**: 6 CRITICAL IRC sections for Aristotle resubmission

---

## EXECUTIVE SUMMARY

Three AI systems (Grok-4, Gemini, Codex) independently reviewed the resubmission strategy. **Consensus**: Strategy is directionally correct but has **critical technical and architectural gaps** that will cause failures if not addressed.

### 🚨 CRITICAL BLOCKERS (Must Fix Before Resubmission)

1. **No Shared Type System** - Each section redefines Currency, TaxYear, FilingStatus → type mismatches
2. **Missing Imports** - Prompts don't specify required Mathlib or project imports
3. **Section 401 Overwrite Risk** - Will delete existing coverage/nondiscrimination code
4. **Underspecified Numeric Types** - Nat-only causes underflows; Currency undefined
5. **Interface Inconsistency** - §152 structure names may not match §21/§24/§32/§151 expectations

### ✅ VALIDATED DECISIONS

- ✅ Priority order: 152 → 1001 → 1221 → 151 → 1012 → 401 (all three AIs agree)
- ✅ §152 as blocker for multiple sections (correct)
- ✅ Core structures/functions identified for each section (directionally sound)
- ✅ Root cause analysis (accurate)

---

## DETAILED ANALYSIS BY SECTION

### Section 151 - Personal Exemptions

| Issue | Source | Severity | Fix |
|-------|--------|----------|-----|
| **Nat-only monetary fields cause underflow** | Codex | CRITICAL | Use `Money := Int` not `Nat` for MAGI calculations |
| **Missing inflation adjustments post-2029** | Codex | HIGH | Add COLA table parameters for §151(d)(5) |
| **Redefines TaxYear instead of reusing** | Codex | MEDIUM | Import existing TaxYear from common module |
| **Duplicate type definitions** | Gemini | HIGH | FilingStatus, Taxpayer already exist elsewhere |
| **Missing imports** | Gemini | CRITICAL | Prompt must specify `import Mathlib` etc. |

**Codex Recommendation**:
```lean
-- DON'T:
structure Taxpayer where
  age : Nat
  MAGI : Nat  -- WILL UNDERFLOW when MAGI < threshold

-- DO:
structure Taxpayer where
  age : Nat
  MAGI : Money  -- where Money := Int (shared type)
```

**Gemini Recommendation**:
- Create `TaxCommon.lean` with Currency, TaxYear, FilingStatus, Taxpayer
- Modify prompt: "Import TaxCommon and use these types (do NOT redefine)"

---

### Section 152 - Dependent Defined

| Issue | Source | Severity | Fix |
|-------|--------|----------|-----|
| **String identifiers prevent decidable equality** | Codex | CRITICAL | Use enums (Relationship, FailureReason) not Strings |
| **Missing residency exceptions** | Codex | HIGH | Add temporary absence, kidnapped child rules |
| **Missing tie-breaker hierarchy §152(c)(4)** | Codex | HIGH | Implement parent vs highest AGI tie-breaker |
| **Generic dependency resolver won't work** | Codex | MEDIUM | Use `DependentUsage` record to track which credit consumed status |
| **API instability breaks §21/§24/§32/§151** | Gemini | CRITICAL | Structure names must match expectations |

**Codex Recommendation**:
```lean
-- DON'T:
structure DependentTestResult where
  isQualifying : Bool
  failureReasons : List String  -- Not decidable!

-- DO:
inductive FailureReason
  | AgeTooHigh | InsufficientResidency | ExcessiveSelfSupport
  deriving DecidableEq, Repr

structure DependentTestResult where
  isQualifying : Bool
  failureReasons : List FailureReason
```

**Gemini Recommendation**:
- **HIGHEST RISK** - This section blocks 4 others
- Must validate API compatibility: Do §21, §24, §32, §151 expect `QualifyingChild` or `Dependent`?
- Add persistent test file `Tests/Test_Section152.lean` to prevent regressions

---

### Section 401 - Qualified Pension Plans

| Issue | Source | Severity | Fix |
|-------|--------|----------|-----|
| **WILL OVERWRITE existing coverage logic** | Gemini | CRITICAL | Prompt MUST include full current code: "Retain ALL existing logic and ADD..." |
| **AccountBalance/Currency types undefined** | Codex | CRITICAL | Ground vesting math on Int/Rat, use uniform Money type |
| **Only 5 of 36 requirements** | Codex | HIGH | Missing §401(a)(13) loans, §411(d)(6) anti-cutback, §415 limits |
| **Hardcoded 2023 amounts** | Codex | MEDIUM | Use data records per tax year, not hardcoded literals |
| **Missing cross-refs to §410, §411, §415** | Codex | MEDIUM | Add Optional fields for these requirements |

**Gemini Recommendation**:
```
WRONG PROMPT:
"Extend IRC §401 formalization: Add 5 critical qualification requirements..."
↑ This will DELETE existing coverage/nondiscrimination functions!

CORRECT PROMPT:
"Here is the current Section401.lean: [FULL FILE]. Retain ALL existing
logic (coverage, nondiscrimination) and ADD the following 5 requirements..."
```

**Codex Recommendation**:
```lean
-- DON'T:
let contribution_limit := 22500  -- Hardcoded for 2023 only!

-- DO:
structure ContributionLimits where
  year : TaxYear
  base : Money
  catchUp50Plus : Money

def contribution_limits_2023 : ContributionLimits :=
  { year := 2023, base := 22500, catchUp50Plus := 7500 }
```

---

### Section 1001 - Gain/Loss Determination

| Issue | Source | Severity | Fix |
|-------|--------|----------|-----|
| **Currency type completely unspecified** | Codex | CRITICAL | Define Money := Int in shared module |
| **Missing liability assumptions §1001(b)(2)** | Codex | HIGH | Add optional field for liabilities in AmountRealized |
| **Missing installment sales §453** | Codex | MEDIUM | Add recognition exceptions field |
| **Duplicate TransactionDetails** | Codex | MEDIUM | Share with §1012 to avoid duplicate basis data |
| **Complex basis adjustments risk errors** | Gemini | MEDIUM | Add persistent test cases for edge cases |

**Codex Recommendation**:
```lean
-- DON'T:
structure AmountRealized where
  money : Currency  -- What IS Currency?!
  fmvProperty : Currency
  taxAdjustments : Currency

-- DO:
structure AmountRealized where
  money : Money
  fmvProperty : Money
  taxAdjustments : Money
  liabilitiesAssumed : Option Money  -- §1001(b)(2)
```

---

### Section 1012 - Cost Basis

| Issue | Source | Severity | Fix |
|-------|--------|----------|-----|
| **Property type conflicts with §1221** | Codex | CRITICAL | Import same PropertyType enum, don't duplicate |
| **Missing stock splits, wash sales** | Codex | HIGH | Add hooks for §§1014/1015 gift basis adjustments |
| **Missing §1223 holding period** | Codex | MEDIUM | Add acquisition date tracking |
| **Duplicate RealEstateTaxes logic** | Codex | MEDIUM | Share helper lemma with §1001 |
| **Account-by-account complexity** | Gemini | MEDIUM | Test with RIC (regulated investment company) scenarios |

**Codex Recommendation**:
```lean
-- DON'T:
structure Property where  -- Conflicts with §1221!
  type : PropertyType

-- DO:
import Section1221 (PropertyType)  -- Reuse!

structure CostBasisProperty where
  propertyType : PropertyType
  acquisitionDate : TaxYear
  costBasis : Money
  giftBasisAdjustment : Option Money  -- §§1014/1015
```

---

### Section 1221 - Capital Asset Defined

| Issue | Source | Severity | Fix |
|-------|--------|----------|-----|
| **Enum can't handle mixed-use assets** | Codex | CRITICAL | Use predicates, not enum-only |
| **Missing hedging identification §1221(b)** | Codex | HIGH | Add boolean for identification statement |
| **Missing §1231 cross-reference** | Codex | HIGH | Character reclassification for depreciables |
| **Duplicate characterFromSections logic** | Codex | MEDIUM | Share function with §§1001/1231 |
| **8 exclusions but no priorities** | Gemini | MEDIUM | What if property matches multiple exclusions? |

**Codex Recommendation**:
```lean
-- DON'T:
inductive PropertyType
  | Capital | Inventory | Depreciable | ...
  -- Can't represent "mostly inventory, partially investment"!

-- DO:
structure PropertyCharacterization where
  isInventory : Bool
  isDepreciable : Bool
  isCreatorHeld : Bool
  -- ... 8 exclusion predicates

def isCapitalAsset (p : PropertyCharacterization) : Bool :=
  !(p.isInventory || p.isDepreciable || ... )  -- Explicit logic
```

---

## ARCHITECTURAL RECOMMENDATIONS

### 1. Create Shared Type Module (CRITICAL)

**File**: `src/TaxCode/TaxCommon.lean`

```lean
-- Currency represented in cents
def Money := Int

-- Tax Year with validation
structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq

-- Filing Status
inductive FilingStatus
  | Single | MarriedFilingJointly | MarriedFilingSeparately
  | HeadOfHousehold | QualifyingWidower
  deriving DecidableEq, Repr, Inhabited

-- Common taxpayer structure
structure Taxpayer where
  id : String
  filingStatus : FilingStatus
  taxYear : TaxYear
  deriving DecidableEq
```

**Action**: Create this file BEFORE any resubmissions. Update ALL prompts to:
```
Import TaxCommon at the top of the file. Use Money (not Currency/Nat),
TaxYear, FilingStatus, Taxpayer from TaxCommon. DO NOT redefine these types.
```

### 2. Update Section 401 Prompt (CRITICAL)

**Current Prompt** (WRONG):
```
Extend IRC §401 formalization: Add 5 critical qualification requirements...
```

**Fixed Prompt**:
```
Here is the current Section401.lean file with existing coverage and
nondiscrimination logic:

[INSERT FULL CURRENT FILE CONTENTS]

IMPORTANT: Retain ALL existing functions (check_coverage_410,
check_nondiscrimination, is_qualified_plan).

Now ADD the following 5 qualification requirements to the Plan structure...
```

### 3. Add Persistent Test Files (HIGH PRIORITY)

For each section, create `Tests/Test_SectionXXX.lean`:

**Example for Section 152**:
```lean
import TaxCode.Section152
import TaxCode.TaxCommon

-- Test case: 17-year-old child, 8 months residency, 40% self-support
def testChild : Person := {
  id := "child1",
  age := 17,
  relationshipType := Relationship.Child,
  residencyMonths := 8,
  selfSupportPct := 40
}

#eval validateQualifyingChild testChild
-- Expected: { isQualifying := true, failureReasons := [] }

-- Test case: Parent AGI tie-breaker
-- ... more test cases
```

**Benefits**:
- Prevents regressions when extending sections
- Validates API compatibility across sections
- Catches edge cases early

### 4. Cross-Section Dependency Map

**Create**: `src/TaxCode/DEPENDENCIES.md`

```
Section 152 (Dependent Defined) IS USED BY:
  → Section 21 (Child Care Credit) - expects QualifyingChild
  → Section 24 (Child Tax Credit) - expects QualifyingChild
  → Section 32 (EITC) - expects QualifyingChild, QualifyingRelative
  → Section 151 (Personal Exemptions) - expects dependent count

Section 1001 (Gain/Loss) IS USED BY:
  → Section 1012 (Cost Basis) - provides adjusted basis
  → Section 1221 (Capital Asset) - provides amount realized

Section 1221 (Capital Asset) IS USED BY:
  → Section 1001 (Gain/Loss) - determines character (capital vs ordinary)
  → Section 1231 (Property Used in Trade/Business)
```

**Action**: Before modifying any section, check DEPENDENCIES.md to understand impact.

---

## UPDATED RESUBMISSION PRIORITY

Based on multi-AI analysis:

### Phase 1: Foundation (DO FIRST)
1. **Create TaxCommon.lean** - Shared types (Money, TaxYear, FilingStatus, Taxpayer)
2. **Create DEPENDENCIES.md** - Document cross-section dependencies
3. **Create Tests/** directory structure

### Phase 2: Critical Blockers
4. **Section 152** - Highest risk, blocks 4 sections
   - Use enums not Strings
   - Add residency exceptions
   - Implement tie-breaker hierarchy
   - Validate API matches §21/§24/§32/§151 expectations

5. **Section 1001** - Foundation for capital gains
   - Define Money type first
   - Add liability assumptions
   - Share TransactionDetails with §1012

### Phase 3: Complementary Sections
6. **Section 1221** - Determines character
   - Use predicates not enum-only
   - Add hedging identification
   - Share with §1001/§1231

7. **Section 1012** - Cost basis
   - Import PropertyType from §1221
   - Add stock split/wash sale hooks
   - Share RealEstateTaxes with §1001

### Phase 4: Standalone Sections
8. **Section 151** - Personal exemptions
   - Use Money not Nat
   - Add COLA parameters
   - Import TaxYear from common

### Phase 5: Extension (Not Full Resubmission)
9. **Section 401** - Qualified pension plans
   - **Include full current file in prompt**
   - Add 5 requirements without deleting existing code
   - Use data records not hardcoded amounts

---

## REVISED PROMPT TEMPLATE

For each section, use this template:

```markdown
### CONTEXT
- Import TaxCommon (Money, TaxYear, FilingStatus, Taxpayer)
- Import Mathlib
- This section is used by: [list dependent sections]

### REQUIREMENTS
[IRC legal requirements]

### STRUCTURES
[From analysis, using Money not Nat/Currency]

### FUNCTIONS
[From analysis, using shared types]

### CROSS-REFERENCES
- Must be compatible with Section X structure Y
- Shares Z with Section W

### VALIDATION
- Include 3-5 test cases as #eval examples
- Prove at least 2 theorems (no 'sorry')
- End with compilation check, no placeholder

### EXAMPLE
[Concrete example with expected output]
```

---

## RISK MITIGATION CHECKLIST

Before submitting to Aristotle:

- [ ] TaxCommon.lean created and committed
- [ ] All prompts updated to import TaxCommon
- [ ] Section 401 prompt includes FULL current file
- [ ] Dependency map created (DEPENDENCIES.md)
- [ ] Test file structure created (Tests/)
- [ ] Numeric types verified (Money := Int everywhere)
- [ ] Cross-section APIs verified for compatibility
- [ ] Each prompt includes concrete examples
- [ ] Each prompt specifies "no placeholder" requirement

---

## COMPARATIVE ANALYSIS SUMMARY

| AI | Strength | Key Insight |
|---|---|---|
| **Grok-4** | Legal requirements | Identified core structures/functions for each section |
| **Gemini** | Integration risks | Found type duplication, missing imports, §401 overwrite risk |
| **Codex** | Lean 4 technical details | Caught Nat underflows, String non-decidability, type conflicts |

**Consensus**: All three AIs agree:
1. ✅ Priority order is correct (152 first)
2. ❌ Type system must be unified BEFORE resubmissions
3. ❌ Section 401 prompt will delete existing code
4. ❌ Missing critical legal provisions in several sections

---

## EXPECTED OUTCOMES

**Before fixes**:
- 6 resubmissions → likely 3-4 compile failures
- Type mismatches across sections
- §401 loses existing functionality
- Integration failures when sections try to use each other

**After fixes**:
- 6 resubmissions → 5-6 successful compilations (83-100% success rate)
- Unified type system enables cross-section integration
- §401 retains AND extends functionality
- Test suites prevent future regressions

**Production-Ready Projection**:
- Current: 15/25 (60%)
- After resubmissions: 20-21/25 (80-84%)
- **Target achieved**: Move from 32% CRITICAL to <8% CRITICAL

---

## NEXT IMMEDIATE ACTIONS

1. **CREATE** `src/TaxCode/TaxCommon.lean` (15 min)
2. **CREATE** `src/TaxCode/DEPENDENCIES.md` (10 min)
3. **CREATE** `Tests/` directory structure (5 min)
4. **UPDATE** Section 401 prompt with full current file (10 min)
5. **UPDATE** all 6 prompts to import TaxCommon (20 min)
6. **VALIDATE** cross-section API compatibility for §152 (15 min)

**Total prep time**: ~75 minutes before first Aristotle resubmission

---

**Document Status**: READY FOR IMPLEMENTATION
**Confidence Level**: HIGH (three independent AI reviewers concur)
**Last Updated**: 2025-12-12 via Grok-4 + Gemini + Codex (GPT-5) analysis
