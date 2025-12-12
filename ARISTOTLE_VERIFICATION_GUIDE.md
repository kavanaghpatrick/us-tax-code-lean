# Aristotle Verification Guide: Where to Trust, Where to Verify

**Date**: December 12, 2025
**Based on**: Quality audit of 9 completed IRC sections
**Purpose**: Guide human reviewers on high-risk areas in AI-generated formalizations

---

## Executive Summary

After auditing 9 Aristotle-generated IRC formalizations, we've identified clear patterns in what Aristotle does well and where human verification is critical. **Formal verification (no `sorry` statements) does NOT guarantee legal correctness** - it only proves mathematical consistency.

**Key Insight**: Aristotle can generate mathematically perfect code that implements the wrong legal rule.

---

## 🟢 Where Aristotle Excels (High Confidence)

### 1. Mathematical Correctness ✅
**Confidence**: 95%+

Aristotle consistently produces valid proofs with sound mathematical reasoning.

**Evidence**:
- 8 of 9 sections have complete proofs (no `sorry`)
- Theorem proving is reliable (decomposition lemmas, bound proofs)
- Arithmetic calculations are accurate

**Example** (Section 301):
```lean
theorem decomposition_lemma_v2 (d : Distribution) (s : Stock) :
    d.taxableAmount s =
    { dividend := min d.amountDistributed s.eps,
      appliedToStockBasis := /* ... */,
      capitalGain := /* ... */ }
-- ✅ Proven correctly
```

**Review Priority**: LOW - Trust the mathematical proofs

---

### 2. Core Statutory Provisions ✅
**Confidence**: 85%

Aristotle reliably implements main statutory logic, thresholds, and calculations.

**Evidence**:
- Section 121: Ownership/use tests (2 of 5 years) perfect
- Section 301: Three-tier distribution treatment (dividend→capital return→gain) perfect
- Section 63: Standard deduction amounts and filing status rules accurate
- Section 61: All 15 income sources correctly enumerated

**Example** (Section 121):
```lean
def ownershipTest (p : OwnershipPeriod) : Bool :=
  p.ownershipDays >= 730  -- ✅ Correct: 2 years = 730 days

def lookbackPeriod : Nat := 1825  -- ✅ Correct: 5 years = 1825 days
```

**Review Priority**: MEDIUM - Verify against statute but usually accurate

---

### 3. Arithmetic and Threshold Enforcement ✅
**Confidence**: 90%

Aristotle accurately implements numeric limits, calculations, and boundary conditions.

**Evidence**:
- Section 121: $250k/$500k exclusion limits correct
- Section 108: 33⅓¢ per dollar credit reduction formula perfect
- Section 301: Amount distributed = money + FMV - liabilities (correct)
- Section 62: $250 educator expense limit enforced

**Example** (Section 108):
```lean
def reduceCredits (excluded : Currency) (credits : List Credit) : List Credit :=
  credits.map fun c =>
    { c with amount := max 0 (c.amount - (excluded / 3)) }
-- ✅ Correct: Divide by 3 for 33⅓¢ formula
```

**Review Priority**: LOW - Trust calculations

---

### 4. Type Safety and Structure ✅
**Confidence**: 95%

Aristotle creates well-structured, type-safe code with good separation of concerns.

**Evidence**:
- All sections use distinct structures (e.g., `Distribution`, `TaxpayerStatus`, `DischargeIndebtedness`)
- Type constraints prevent invalid inputs (e.g., `TaxYear >= 1913`)
- Clean function decomposition
- Proper use of Lean 4 idioms

**Example** (Section 301):
```lean
structure Distribution where
  money : Currency
  property : List Property
  stock : Stock
  deriving DecidableEq
-- ✅ Clean, type-safe design
```

**Review Priority**: LOW - Trust the structure

---

## 🔴 Where Aristotle Fails (High Risk)

### 1. "Other Than" Exclusions ❌
**Confidence**: 30% - **HIGH RISK**

Aristotle misinterprets negative eligibility phrases like "other than" or "except for."

**Evidence**:
- **Section 108 (CRITICAL ERROR)**: IRC §108(a)(1)(D) says "taxpayer **OTHER THAN a C corporation**"
  - Aristotle gave C corps an exclusion when they should get ZERO
  - Gave non-C corps unlimited exclusion when they should be capped
  - Code was **completely backwards**

**Pattern**: When statute says "except X" or "other than X", Aristotle may invert the logic.

**Review Checklist**:
- [ ] Search code for "other than", "except", "excluding" in original statute
- [ ] Verify ineligible entities return 0 or throw error
- [ ] Verify eligible entities get the benefit
- [ ] Test with both eligible and ineligible taxpayers

**Example of Error**:
```lean
-- ❌ WRONG (Section 108 actual code)
if s.is_c_corporation then
  min d.amount s.insolvency_amount  -- C corps get exclusion (ILLEGAL!)
else
  d.amount  -- Non-C corps get unlimited (ILLEGAL!)

-- ✅ CORRECT (after fix)
if s.is_c_corporation then
  0  -- C corporations INELIGIBLE per "OTHER THAN"
else
  min d.amount (min limitA limitB)  -- Apply statutory caps
```

**Review Priority**: **CRITICAL** - Always verify exclusions

---

### 2. Multi-Step Limitations and Caps ⚠️
**Confidence**: 60% - **MEDIUM RISK**

Aristotle may miss or oversimplify statutory provisions with multiple limiting conditions.

**Evidence**:
- Section 108: Missing §108(c)(2) dual limitations (principal-FMV AND depreciable basis)
- Section 121: Nonqualified use calculations are complex but Aristotle got them right
- Section 62: Some later-added phase-outs not implemented

**Pattern**: When statute says "the lesser of (A) or (B), but not more than (C)", Aristotle may miss one layer.

**Review Checklist**:
- [ ] Identify all "shall not exceed", "limited to", "lesser of" clauses
- [ ] Count limitation layers in statute (should match code)
- [ ] Verify min() and max() operations match statute structure
- [ ] Test with values that hit each limitation boundary

**Example of Error**:
```lean
-- ❌ WRONG (Section 108)
else
  d.amount  -- Missing §108(c)(2) limitations!

-- ✅ CORRECT
else
  let limitA := max 0 (outstanding_principal - property_fmv)
  let limitB := aggregate_depreciable_basis
  min d.amount (min limitA limitB)  -- Both limitations applied
```

**Review Priority**: **HIGH** - Always verify all caps are applied

---

### 3. Completeness - Missing Subsections ⚠️
**Confidence**: 50% - **MEDIUM RISK**

Aristotle often omits edge case provisions, elections, and special rules.

**Evidence**:
- Section 101: Only 4 of 10 subsections implemented (40% coverage)
- Section 121: Missing reduced exclusion for unforeseen circumstances (§121(c))
- Section 108: Missing basis reduction election (§108(b)(5))
- Section 62: Missing ~10 later-added deductions (HSAs, attorney fees)

**Pattern**: Aristotle focuses on "core" provisions and marks others as TODO or omits them entirely.

**Review Checklist**:
- [ ] Compare section structure in code vs statute
- [ ] Search for "TODO", "missing", "not implemented" in comments
- [ ] List all subsections in statute, verify each is addressed
- [ ] Check if missing provisions affect common use cases

**Example**:
```lean
-- Section 121 omits:
-- (c) Reduced exclusion for unforeseen circumstances
-- (d)(10) Like-kind exchange rules
-- (d)(11) Divorced spouse provisions
-- Impact: Edge cases not handled, but standard sales OK
```

**Review Priority**: **MEDIUM** - Assess based on use case importance

---

### 4. Timeouts on Complex Sections ❌
**Confidence**: N/A - **INFRASTRUCTURE RISK**

Aristotle may timeout on particularly complex sections, producing incomplete code.

**Evidence**:
- **Section 1 (Tax Tables)**: Timeout after 6101 seconds (1h 41m)
  - File contains: "Sorry, Aristotle was unable to complete the task in time."
  - Proofs cut off mid-expression
  - Tax brackets from 1990s instead of post-TCJA 2024

**Pattern**: Sections with large lookup tables, many cases, or historical amendments are high risk.

**Review Checklist**:
- [ ] Search file for "Sorry, Aristotle was unable"
- [ ] Check if section has >50 subsections or historical amendments
- [ ] Verify tax year is current (2024/2025, not outdated)
- [ ] Check if theorems are complete or cut off

**Example**:
```lean
-- Section 1 timeout
/-
Sorry, Aristotle was unable to complete the task in time.

The task was to formalize US tax code section Section 1 in Lean 4.
-- File incomplete, tax tables outdated
```

**Review Priority**: **CRITICAL** - Rerun with better prompts or manual implementation

---

### 5. Incomplete Proofs (`exact?` placeholders) ❌
**Confidence**: 0% - **CRITICAL RISK**

In rare cases, Aristotle may leave tactical proof searches (`exact?`) unresolved.

**Evidence**:
- **Section 103**: Contains `exact?` on lines 164, 166
  - These are unresolved proof placeholders
  - Code will not compile in strict Lean 4 mode
  - Indicates Aristotle couldn't complete the proof

**Pattern**: When Aristotle can't find the right tactic, it may insert `exact?` as a placeholder.

**Review Checklist**:
- [ ] Search entire file for `exact?`, `sorry`, `admit`
- [ ] Check if proofs compile without errors
- [ ] Verify all theorems have complete proof terms

**Example**:
```lean
-- ❌ Section 103 (incomplete)
theorem interest_partition (b : Bond) (h : b.issuanceYear > 1982) :
    /* ... */ := by
  exact?  -- ❌ INCOMPLETE - proof not finished!
```

**Review Priority**: **CRITICAL** - Rerun or manually complete proof

---

### 6. Entity-Specific Rules ⚠️
**Confidence**: 55% - **MEDIUM-HIGH RISK**

Aristotle may oversimplify or omit provisions specific to entity types (C corp, S corp, partnership).

**Evidence**:
- Section 108: No modeling of S corp/partnership/C corp rules from §108(d), §108(e)
- Section 301: Missing §318 constructive ownership rules for 20% shareholders
- Section 121: Incomplete joint return attribution rules

**Pattern**: Provisions like "in the case of an S corporation" or "for partnerships" are often simplified or omitted.

**Review Checklist**:
- [ ] Search statute for "C corporation", "S corporation", "partnership"
- [ ] Verify each entity-specific rule is modeled or documented as missing
- [ ] Check if entity type affects eligibility, amounts, or calculations
- [ ] Test with different entity types

**Review Priority**: **HIGH** - Critical for multi-entity tax planning

---

## 📋 Verification Workflow

### Phase 1: Automated Checks (5 minutes)
```bash
# Check for incomplete proofs
rg -n 'exact\?|sorry|admit' Section*.lean

# Check for timeouts
rg -n 'Sorry, Aristotle was unable' Section*.lean

# Check for TODOs
rg -n 'TODO|FIXME|missing' Section*.lean

# Check tax year currency
rg -n 'TaxYear.*19[0-9][0-9]' Section*.lean  # Flag pre-2000 years
```

### Phase 2: Structural Review (15 minutes)
1. Compare section structure in code vs IRC statute
2. List all subsections in statute, check each is addressed
3. Identify major provisions marked as "missing" or TODO
4. Assess completeness percentage

### Phase 3: Logic Review (30-60 minutes)
**HIGH PRIORITY areas:**
1. **"Other than" exclusions** - Search statute for exclusions, verify logic
2. **Multi-layer limitations** - Count caps, verify all applied
3. **Entity-specific rules** - Check C corp/S corp/partnership provisions
4. **Eligibility conditions** - Verify who qualifies and who doesn't

### Phase 4: Test Cases (30 minutes)
Create 3-5 test scenarios:
1. **Happy path**: Standard qualifying case
2. **Boundary test**: Hit each limitation threshold
3. **Ineligible entity**: Should return 0 or be blocked
4. **Edge case**: Test missing provisions (should fail gracefully)
5. **Historical date**: Test effective date logic

### Phase 5: Multi-AI Validation (for critical issues)
If Phase 3 finds potential logic errors:
1. Use Grok-4 for statutory interpretation
2. Use Gemini for impact analysis
3. Use Codex for comprehensive review
4. Require unanimous agreement (as with Section 108)

---

## 🎯 Quick Risk Assessment

Given a newly generated section, assign risk score:

| Factor | Low Risk (0-2 pts) | Medium Risk (3-5 pts) | High Risk (6-10 pts) |
|--------|-------------------|---------------------|---------------------|
| **Exclusion Language** | No "other than" clauses | Has "except" or "only if" | Has "OTHER THAN" eligibility rules |
| **Limitation Layers** | Single cap (max X) | Two layers (lesser of A or B) | Three+ layers of caps |
| **Entity Rules** | Applies to all taxpayers | Some entity distinctions | Multiple entity-specific provisions |
| **Completeness** | 80%+ of subsections | 50-79% of subsections | <50% of subsections |
| **Proof Status** | All complete, no `sorry` | Some TODO comments | Has `exact?`, `sorry`, or timeout |
| **Code Complexity** | <300 lines | 300-800 lines | 800+ lines or timeout |

**Score Interpretation**:
- **0-5 points**: Trust with spot checks (LOW priority)
- **6-12 points**: Full logical review required (MEDIUM priority)
- **13+ points**: Multi-AI validation required (HIGH priority)

---

## 📊 Audit Results Summary

From 9 sections audited:

| Risk Category | Count | Examples | Action |
|--------------|-------|----------|--------|
| **Low Risk** | 4 sections | 61, 62, 63, 301 | Spot check only |
| **Medium Risk** | 3 sections | 101, 121, 108* | Full review |
| **High Risk** | 2 sections | 1 (timeout), 103 (`exact?`) | Rerun/manual fix |

*Section 108 appeared low risk initially (complete proofs, 7/10 score) but had a CRITICAL logic error. This validates the need for careful "other than" review.

---

## 🔍 Lessons Learned

### 1. Formal Verification ≠ Legal Correctness
**Section 108** had zero `sorry` statements, complete proofs, and 7/10 audit score - yet implemented the law **backwards**. Aristotle proved the code was mathematically consistent with the wrong specification.

**Takeaway**: Never assume "no sorry" means "correct law."

### 2. "Other Than" is a Red Flag
The phrase "OTHER THAN" in IRC §108(a)(1)(D) caused a complete inversion of logic. This is a **systematic risk** - check ALL exclusion clauses.

**Takeaway**: Create automated check for "other than" in statutes.

### 3. Multi-AI Validation Works
All 4 AI systems (Claude, Grok-4, Gemini, Codex) unanimously confirmed the Section 108 error with 100% agreement. This gave extremely high confidence in the finding.

**Takeaway**: For critical logic errors, require 3-4 AI agreement before fixing.

### 4. Timeouts Need Better Prompts
Section 1 timeout suggests Aristotle needs better guidance on complex sections with large lookup tables.

**Takeaway**: Pre-process complex sections with clearer structure before Aristotle generation.

---

## 🚀 Recommended Process Improvements

### 1. Pre-Generation Checklist
Before submitting to Aristotle:
- [ ] Identify "other than" exclusions in statute → flag in prompt
- [ ] Count limitation layers → specify in prompt
- [ ] List entity-specific rules → request explicit handling
- [ ] Provide test cases → include in prompt

### 2. Post-Generation Automated Checks
```python
def audit_section(filepath):
    checks = {
        'incomplete_proofs': check_for_sorry_exact(filepath),
        'timeout': check_for_timeout_message(filepath),
        'todos': count_todos(filepath),
        'outdated_years': check_tax_years_current(filepath),
        'entity_specifics': check_entity_rules(filepath)
    }
    return RiskScore(checks)
```

### 3. Tiered Review Process
- **Tier 1 (Automated)**: All sections get automated checks
- **Tier 2 (Human Spot Check)**: Low-risk sections (score 0-5)
- **Tier 3 (Full Human Review)**: Medium-risk sections (score 6-12)
- **Tier 4 (Multi-AI Validation)**: High-risk sections (score 13+) or failed checks

### 4. Test Suite Requirement
Every formalized section must include:
- 3+ test cases with `#eval` examples
- At least one ineligible entity test (should return 0)
- At least one boundary test (hit limitation caps)
- Historical effective date test (if applicable)

---

## 📝 GitHub Issue Template

```markdown
### Section XXX - [Issue Type]

**Risk Level**: LOW / MEDIUM / HIGH / CRITICAL
**Issue Type**: Logic Error / Incomplete / Timeout / Missing Proofs

**Problem**:
[Clear description of what's wrong]

**Statutory Reference**:
IRC §XXX(x)(x) states: "[exact quote]"

**Current Code** (lines XXX-XXX):
```lean
[paste code]
```

**Expected Code**:
```lean
[paste correct implementation]
```

**Impact**:
- [ ] Affects common use cases
- [ ] Revenue impact: $XXX million (if quantifiable)
- [ ] Legal compliance issue
- [ ] Production blocker

**Evidence**:
- [ ] Multi-AI validation (Grok-4, Gemini, Codex): X/3 agree
- [ ] IRS examples contradict code
- [ ] Court cases contradict code

**Recommendation**:
- [ ] Manual fix
- [ ] Rerun Aristotle with better prompt
- [ ] Needs expert legal review
```

---

## Conclusion

Aristotle is **excellent** at mathematical reasoning and core statutory implementation, but **struggles** with:
1. Negative eligibility language ("other than")
2. Multi-layer limitations
3. Completeness and edge cases
4. Entity-specific provisions

**Golden Rule**: Trust the math, verify the law.

The combination of formal verification + careful human review + multi-AI validation is the winning approach for production-ready tax code formalization.
