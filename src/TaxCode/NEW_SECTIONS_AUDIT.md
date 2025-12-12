# Multi-AI Audit: New IRC Sections (301, 482, 401, 2001, 2501)

**Date**: 2025-12-12
**Auditors**: Grok-4, Gemini 2.5 Flash
**Sections Audited**: 5 new completions from Priority-50 queue

## Executive Summary

All 5 new sections were audited by both Grok-4 and Gemini to provide comprehensive quality assessment.

| Section | Grok Score | Gemini Score | Consensus | Recommendation |
|---------|-----------|--------------|-----------|----------------|
| 301 | 6/10 (MODERATE) | 8/10 (GOOD) | 7/10 GOOD | NEEDS-WORK |
| 482 | 7/10 (GOOD) | 7/10 (GOOD) | 7/10 GOOD | NEEDS-WORK |
| 401 | 6/10 (MODERATE) | 7/10 (GOOD) | 6.5/10 GOOD | NEEDS-WORK |
| 2001 | 5/10 (MODERATE) | 6/10 (MODERATE) | 5.5/10 MODERATE | NEEDS-WORK |
| 2501 | 6/10 (GOOD) | 7/10 (GOOD) | 6.5/10 GOOD | NEEDS-WORK |

**Key Finding**: All sections require additional work before production use. No sections achieved EXCELLENT status.

---

## Section 301: Distributions of Property

### Grok-4 Assessment
**Score**: 6/10 (MODERATE) - NEEDS-WORK

**Strengths**:
- Solid foundational structures for Property, Stock, and Distribution, aligning with IRC §301's focus on distributions and basis
- Includes key theorems (e.g., non-negativity and equality checks) to verify calculation logic
- Incorporates examples and uses Mathlib for formal proofs

**Issues**:
- Currency defined as Int lacks decimal precision (e.g., for cents), risking inaccuracies in real tax computations
- Only 2 theorems for verification; more proofs needed for edge cases
- Structures are basic but lack integration with broader tax contexts (e.g., no links to earnings & profits or shareholder types)
- File size and def count suggest incomplete implementation

**Missing Provisions**:
- Handling of constructive dividends or non-qualified distributions under §301(a)
- Special rules for foreign corporations or accumulated earnings in §301(f)
- Integration with related sections like §316 (dividend definitions) or §317 (property definitions)

### Gemini Assessment
**Score**: 8/10 (GOOD)

**Strengths**:
- **Formal Verification**: Includes rigorous theorems (`taxableAmount_sum_eq_amountDistributed` and `amountDistributed_nonneg`) that mathematically prove the accounting logic
- **Accurate "Waterfall" Logic**: The `calculateTaxableAmount` function correctly implements the priority order of § 301(c)
- **Clean Abstractions**: The separation of `Distribution`, `Property`, and `Stock` structures is well-designed

**Issues**:
- **Disconnected § 301(e) Logic**: While `isTwentyPercentCorporateShareholder` is defined, it is completely unused in the calculation logic
- **Abstracted Dividend Determination**: The code takes `dividendPortion` as a static input, abstracting away the complexity of § 316 (Earnings & Profits)
- **Implicit Valuation Timing**: § 301(b)(3) mandates that Fair Market Value is determined "as of the date of the distribution"

**Missing Provisions**:
- **§ 301(e)(1) E&P Adjustment**: The logic to calculate taxable income by ignoring § 311(b) adjustments for 20% corporate shareholders
- **§ 301(f) Special Rules**: Provisions regarding the distribution of antitrust stock are not represented

### Consensus Analysis
**Average Score**: 7/10 (GOOD)

**Critical Issues** (both AIs agree):
1. **§301(e) Implementation Gap**: The 20% corporate shareholder logic is defined but not integrated
2. **Currency Precision**: Int type may not handle fractional amounts accurately
3. **Missing §316 Integration**: Earnings & Profits calculation is abstracted away

**Divergence**: Gemini rated the formal verification and logic structure higher than Grok, suggesting the implementation is solid but incomplete.

**Recommendation**: Add §301(e) adjustments, integrate with §316, add temporal components for valuation timing.

---

## Section 482: Allocations Among Taxpayers

### Grok-4 Assessment
**Score**: 7/10 (GOOD) - NEEDS-WORK

**Strengths**:
- Solid foundational structures (e.g., Organizations, ControlGroups, IntangibleProperty)
- Includes theorems verifying income preservation and commensurate pricing
- Leverages Mathlib for mathematical soundness

**Issues**:
- Logic may oversimplify complex allocations, potentially mismatching nuanced IRS guidelines
- Limited visibility in code sample; full file needed to assess theorem proofs
- No explicit examples or test cases for validation
- Heavy reliance on custom options (e.g., maxHeartbeats) suggests potential performance issues

**Missing Provisions**:
- Detailed transfer pricing methods (e.g., Comparable Uncontrolled Price, Cost Plus)
- Rules for intercompany services, loans, and cost-sharing arrangements
- Penalties and dispute resolution mechanisms under §482

### Gemini Assessment
**Score**: 7/10 (GOOD)

**Strengths**:
- **Accurate Structural Modeling**: The `ControlGroup` definition correctly enforces the statutory requirement of "two or more organizations"
- **Inclusion of Modern Standards**: Explicitly models the "commensurate with income" standard for intangible property transfers
- **Clear Logic Flow**: The use of `determineReliableMethod` effectively captures the Secretary's discretionary logic

**Issues**:
- **Weak Validity Check**: The `isValidReallocation` function relies solely on `list.length`, allowing invalid reallocations
- **Tautological Theorems**: The preservation theorems rely on the hypothesis that income is already preserved, rather than proving the allocation logic enforces conservation
- **Static Pricing Model**: The `isCommensurate` check models the transfer as a static event, missing periodic adjustments
- **Hardcoded Valuation Hierarchy**: The `determineReliableMethod` function enforces a strict hierarchy that may not reflect dynamic statutory interpretation

**Missing Provisions**:
- **Definition of Control**: The code assumes a `ControlGroup` exists by fiat, lacking logic to determine control based on ownership percentages
- **Definition of Intangible Property**: Section 482 applies to specific categories (patents, formulas, know-how, etc.), which are absent

### Consensus Analysis
**Average Score**: 7/10 (GOOD)

**Critical Issues** (both AIs agree):
1. **Weak Reallocation Validation**: `isValidReallocation` only checks list length, not taxpayer identity
2. **Missing Transfer Pricing Methods**: No implementation of CUP, Cost Plus, or other standard methods
3. **Tautological Theorem Proofs**: Theorems assume what they should prove

**Divergence**: Grok focused on missing implementation details (pricing methods, test cases), while Gemini focused on logical flaws in the validation and theorem structure.

**Recommendation**: Strengthen `isValidReallocation` to check taxpayer identity, implement actual transfer pricing methods, rewrite theorems to prove conservation rather than assume it.

---

## Section 401: Qualified Pension, Profit-Sharing Plans

### Grok-4 Assessment
**Score**: 6/10 (MODERATE) - NEEDS-WORK

**Strengths**:
- Solid foundational structures (e.g., TaxYear, Employee) align with tax concepts
- Includes theorems for key properties like coverage and nondiscrimination
- Covers critical calculations (e.g., IRC §410(b) coverage, §401(a)(4) nondiscrimination)

**Issues**:
- Code sample is truncated (e.g., Employee structure incomplete)
- Potential over-simplification: Currency as Int (cents) ignores real-world complexities like inflation adjustments
- Theorems mentioned but not shown; correctness can't be fully verified
- Assumes classical logic and big operators, which may introduce non-constructive elements

**Missing Provisions**:
- Vesting and participation rules under §401(a)(2)-(3), essential for plan qualification
- Distribution and anti-alienation requirements (§401(a)(9), (13))
- Top-heavy plan rules and fiduciary duties (§401(a)(1), related ERISA ties)

### Gemini Assessment
**Score**: 7/10 (GOOD)

**Strengths**:
- **Safe Integer Arithmetic for Ratios**: The implementation of the 410(b) ratio percentage test correctly uses cross-multiplication to avoid floating-point errors
- **Clear Domain Modeling**: The structures for `Employer`, `Employee`, and `Plan` cleanly map to the necessary entities
- **Sanity-Check Theorems**: Includes theorems like `coverage_passed_if_all_benefit` that verify intuitive cases

**Issues**:
- **Oversimplified Nondiscrimination (401(a)(4))**: The `check_nondiscrimination` function relies on comparing average contribution rates, but actual regulations require testing rate groups or meeting specific safe harbor requirements
- **Missing Compensation Limit (401(a)(17))**: The `get_rate` calculation uses raw `e.compensation`, ignoring the statutory limit (e.g., $330,000 for 2023)
- **Potential Compilation Error (Tactics)**: The proof invokes `grind`, which is not a standard stable tactic in current Mathlib4 releases
- **Integer Division in Averages**: The calculation uses integer division, which truncates remainders and may lead to false passes/failures

**Missing Provisions**:
- **Required Minimum Distributions (401(a)(9))**: The code lacks any structure or logic to enforce RMDs
- **Minimum Participation Rule (401(a)(26))**: No check for the "50/40 rule"

### Consensus Analysis
**Average Score**: 6.5/10 (GOOD)

**Critical Issues** (both AIs agree):
1. **Oversimplified Nondiscrimination Test**: Average-based test doesn't match regulatory requirements
2. **Missing Compensation Limits**: §401(a)(17) limits are not enforced
3. **Missing Key Provisions**: No RMD logic (§401(a)(9)), no minimum participation (§401(a)(26))

**Divergence**: Grok focused on missing provisions and truncated code, while Gemini identified specific algorithmic flaws (integer division, missing compensation limits).

**Recommendation**: Implement proper nondiscrimination testing per Treas. Reg. § 1.401(a)(4), add compensation limits, implement RMD and minimum participation rules, fix `grind` tactic to use stable alternatives.

---

## Section 2001: Estate Tax Imposition and Rate

### Grok-4 Assessment
**Score**: 5/10 (MODERATE) - NEEDS-WORK

**Strengths**:
- Includes core elements like rate schedule from §2001(c) and computation logic from §2001(b)
- Uses appropriate Lean 4 features like structures, instances, and Mathlib imports
- Provides an example calculation and TODOs

**Issues**:
- FilingStatus is irrelevant to estate tax (which applies to decedents' estates, not income tax filing categories)
- Currency defined as Int may not handle fractional amounts accurately
- Code sample is truncated (cuts off at "instance : LT")
- Limited scope with only 4 defs and 2 theorems in 9812 bytes suggests underdevelopment
- Assumes tax year starts at 1913, but estate tax history and rates vary

**Missing Provisions**:
- Subsections (d) on credits, (e) on prior transfers, and (f) on valuation (noted as TODOs)
- Integration with related IRC sections (e.g., §2010 unified credit, §2053 deductions)
- Handling of non-resident aliens or special rules for certain estates

### Gemini Assessment
**Score**: 6/10 (MODERATE) - NEEDS-WORK

**Strengths**:
- **Arithmetic Fidelity to 2001(c)**: The implementation of `section2001_c_rate_schedule` correctly encodes the statutory brackets
- **Formal Verification of Economic Properties**: The author attempts to prove `section2001_c_rate_schedule_monotone`
- **Type Aliasing**: The use of `def Currency := Int` allows for potential future refactoring

**Issues**:
- **Fragile and Incomplete Proof Scripts**: The proof for `section2001_c_rate_schedule_monotone` is extremely brittle, relying on `exact?` (which should not be in production code)
- **Oversimplification of 2001(b)(2)**: The `section2001_b_computation` function accepts `aggregate_gift_tax_payable` as a simple integer input, abstracting away the most difficult computational part
- **Irrelevant Data Structures**: The `FilingStatus` inductive type is defined but irrelevant to Section 2001
- **Reliance on `native_decide`**: The proofs use `native_decide +revert`, which does not provide axiomatic proof

**Missing Provisions**:
- **IRC §2001(b)(2) "Hypothetical" Tax Logic**: The code fails to implement the "computation of tax on prior gifts" at current rates
- **IRC §2010 (Unified Credit) Integration**: Without applying the Section 2010 credit, the result is not the actual tax liability

### Consensus Analysis
**Average Score**: 5.5/10 (MODERATE)

**Critical Issues** (both AIs agree):
1. **FilingStatus Irrelevance**: Structure is defined but doesn't apply to estate tax
2. **§2001(b)(2) Oversimplification**: Missing "hypothetical" tax calculation for prior gifts
3. **Brittle Proof Scripts**: Proofs rely on `exact?` and `native_decide` rather than proper arithmetic tactics
4. **Missing §2010 Integration**: No unified credit applied, making the result incomplete

**Divergence**: Grok focused on scope and missing TODOs, while Gemini identified specific proof quality issues and architectural problems.

**Recommendation**: Remove FilingStatus, implement §2001(b)(2) "hypothetical" tax calculation, rewrite proofs using `omega` or structured `linarith`, integrate with §2010 unified credit.

---

## Section 2501: Gift Tax Imposition

### Grok-4 Assessment
**Score**: 6/10 (GOOD) - NEEDS-WORK

**Strengths**:
- Solid foundational structures (e.g., TaxYear, PropertyType, Donor)
- Includes theorems (6 total) for verifying logic against legal text
- Proper Lean 4 practices like custom Repr instances, scoped opens, and noncomputable sections

**Issues**:
- Code sample is truncated (e.g., ForeignCorpInfo incomplete)
- Overly simplistic types (e.g., Currency as Int, voting power as Nat 0-100)
- FilingStatus included but irrelevant to §2501
- High maxRecDepth and synthInstance settings indicate potential performance issues
- Assumes classical logic via open scoped Classical

**Missing Provisions**:
- Exclusions under §2511 (e.g., transfers to political organizations) and integration with annual exclusions (§2503)
- Detailed valuation rules for gifts (e.g., fair market value under §2512) and treatment of split gifts (§2513)
- Handling of trusts, powers of appointment (§2514), or coordination with estate tax (§2502)

### Gemini Assessment
**Score**: 7/10 (GOOD) - NEEDS-WORK

**Strengths**:
- **Accurate Expatriate Look-Through Logic**: Correctly implements the complex mathematical valuation rules for expatriates transferring stock in foreign corporations
- **Robust Definitions for Possessions**: The helper functions accurately capture the nuance of IRC § 2501(b) and (c)
- **Formal Verification**: Includes well-structured theorems that verify the logic against the statutory text

**Issues**:
- **Critical Situs Logic Error**: The `isTaxableTransfer` function returns `true` for *all* tangible property transfers by non-residents. Under IRC § 2511(a), transfers are only taxable if the tangible property is situated **within the United States**
- **Oversimplified Expatriate Status**: The `Donor` structure uses a simple `isExpatriate` boolean, missing the 10-year window and specific tax liability/net worth tests
- **Ambiguous Exempt Organization Definition**: The `toExemptOrg` boolean is too broad
- **Filing Status Unused**: The `FilingStatus` inductive type is defined but never utilized

**Missing Provisions**:
- **Burden of Proof rules**: IRC § 2501(a)(5)(C) imposes a specific burden of proof on the donor
- **Cross-reference to § 2511**: The actual logic for property situs (Location) is not integrated into the taxability determination

### Consensus Analysis
**Average Score**: 6.5/10 (GOOD)

**Critical Issues** (both AIs agree):
1. **Situs Logic Error**: All tangible property transfers by non-residents are taxed, regardless of location
2. **FilingStatus Irrelevance**: Structure is defined but doesn't apply to gift tax
3. **Oversimplified Expatriate Status**: Missing 10-year window and specific tests
4. **Missing §2511 Integration**: Property situs logic is not integrated

**Divergence**: Grok focused on missing provisions (§2503, §2513, §2514), while Gemini identified a critical algorithmic bug in the situs logic.

**Recommendation**: **URGENT**: Fix situs logic to check `property.location` for non-residents. Remove FilingStatus. Add 10-year expatriate window. Integrate with §2511 for property situs rules.

---

## Cross-Cutting Issues

### Issues Present in Multiple Sections

1. **FilingStatus Misuse** (Sections 301, 401, 2001, 2501):
   - All 4 sections define `FilingStatus` but it's only relevant to income tax (Forms 1040), not corporate distributions, estate tax, or gift tax
   - **Action**: Remove FilingStatus from non-income-tax sections

2. **Currency as Int** (All 5 sections):
   - All sections use `Currency := Int`, which may not handle fractional amounts (cents) accurately
   - **Action**: Consider using a decimal or rational type

3. **Missing Integration** (Sections 301, 2001, 2501):
   - Section 301 doesn't integrate with §316 (E&P)
   - Section 2001 doesn't integrate with §2010 (unified credit)
   - Section 2501 doesn't integrate with §2511 (situs rules)
   - **Action**: Create shared modules for cross-referenced sections

4. **Brittle Proof Tactics** (Sections 401, 2001):
   - Section 401 uses `grind` (not stable in Mathlib4)
   - Section 2001 uses `exact?` and `native_decide` (not production-ready)
   - **Action**: Rewrite proofs using stable tactics (`omega`, `linarith`, `aesop`)

5. **Truncated Code Samples** (Sections 301, 401, 2501):
   - Grok noted truncated code in 3 sections
   - **Action**: Verify complete implementations

---

## Priority Recommendations

### Immediate (Critical Bugs)
1. **Section 2501**: Fix situs logic error for tangible property transfers by non-residents
2. **Section 401**: Fix `grind` tactic to use stable alternatives
3. **Section 2001**: Remove irrelevant `FilingStatus` structure
4. **Section 482**: Strengthen `isValidReallocation` to check taxpayer identity, not just list length

### Short-Term (Missing Core Logic)
1. **Section 301**: Integrate §301(e) 20% corporate shareholder adjustments
2. **Section 2001**: Implement §2001(b)(2) "hypothetical" tax calculation for prior gifts
3. **Section 401**: Implement proper nondiscrimination testing per Treas. Reg. § 1.401(a)(4)
4. **Section 2501**: Add 10-year expatriate window and §877(b) tests

### Medium-Term (Integration & Completeness)
1. **Section 301**: Integrate with §316 (Earnings & Profits)
2. **Section 2001**: Integrate with §2010 (unified credit)
3. **Section 2501**: Integrate with §2511 (situs rules)
4. **Section 401**: Add RMD logic (§401(a)(9)) and minimum participation (§401(a)(26))
5. **Section 482**: Implement transfer pricing methods (CUP, Cost Plus, etc.)

### Long-Term (Quality & Robustness)
1. **All Sections**: Consider replacing `Currency := Int` with decimal/rational type
2. **Sections 401, 2001**: Rewrite proofs using stable tactics
3. **Sections 301, 482**: Add comprehensive test cases and examples
4. **All Sections**: Add documentation and cross-references

---

## Comparison with Existing Sections

### Best Performers (Previous Audits)
- Section 21: 8/10 (EXCELLENT) - Child and dependent care credit
- Section 408: 7/10 (GOOD) - Individual retirement accounts

### New Sections Performance
- **No EXCELLENT scores**: Best is Section 301 at 7/10 average (Grok 6/10, Gemini 8/10)
- **One LOW score**: Section 2001 at 5.5/10 average (Grok 5/10, Gemini 6/10)
- **All NEEDS-WORK**: All 5 sections require additional implementation before production use

### Key Differences
1. **Proof Quality**: Best sections have stable, well-documented proofs. New sections use brittle tactics.
2. **Integration**: Best sections integrate with related IRC sections. New sections abstract away dependencies.
3. **Test Coverage**: Best sections have comprehensive examples. New sections have limited test cases.

---

## Conclusion

**Overall Assessment**: The Priority-50 queue produced 5 new sections, but all require significant additional work before production use. The success rate (14/50 = 28%) is concerning, suggesting the batch submission approach may not be optimal.

**Strengths Across All Sections**:
- Strong use of Lean 4 features (structures, theorems, Mathlib)
- Formal verification attempts for key properties
- Generally accurate encoding of statutory language

**Weaknesses Across All Sections**:
- Missing integration with related IRC sections
- Brittle or incomplete proof scripts
- Over-simplified type systems (Currency as Int, boolean flags for complex tests)
- Irrelevant structures (FilingStatus in non-income-tax contexts)

**Next Steps**:
1. Create GitHub issues for each critical bug (Section 2501 situs logic, Section 401 grind tactic, etc.)
2. Update audit_report_full.json with new section entries
3. Update README.md with new statistics (31 sections, 62% complete)
4. Consider revising Aristotle submission strategy to improve success rate
