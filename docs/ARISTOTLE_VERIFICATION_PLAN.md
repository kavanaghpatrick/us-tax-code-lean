# Action Plan: Formal Verification of IRC Tax Code Fixes Using Harmonic Aristotle

## Executive Summary
This plan outlines a systematic approach to use Harmonic Aristotle to generate formal proofs for the 4 recently fixed IRC sections (§162, §103, §32, §24). The strategy focuses on **property-based verification** where we ask Aristotle to generate theorems proving specific correctness properties rather than regenerating entire sections.

---

## Phase 1: Critical Correctness Properties (Priority: IMMEDIATE)

### Section 162 (Business Expenses) - 8/10
**Missing Theorems to Prove**:

1. **Government Fine Non-Deductibility** (§162(f))
   ```lean
   theorem govt_fine_always_zero (e : Expense) :
     e.type = ExpenseType.FineOrPenalty true amt →
     e.ordinary ∧ e.necessary ∧ e.paidOrIncurred ∧ e.tradeOrBusiness →
     deductibleAmount e = 0
   ```

2. **Executive Compensation Cap Enforcement** (§162(m))
   ```lean
   theorem exec_comp_cap_enforced (e : Expense) (amt : Currency) :
     e.type = ExpenseType.ExecutiveCompensation true true amt →
     e.ordinary ∧ e.necessary ∧ e.paidOrIncurred ∧ e.tradeOrBusiness →
     amt > 1000000 →
     deductibleAmount e = 1000000
   ```

3. **Lobbying Complete Disallowance** (§162(e))
   ```lean
   theorem lobbying_always_zero (e : Expense) (direct : Bool) (amt : Currency) :
     e.type = ExpenseType.LobbyingExpense direct amt →
     e.ordinary ∧ e.necessary ∧ e.paidOrIncurred ∧ e.tradeOrBusiness →
     deductibleAmount e = 0
   ```

**Aristotle Prompt**:
```
Generate Lean 4 theorems proving these IRC §162 properties:
1. Government fines (governmentPaid=true) always result in 0 deduction
2. Executive compensation for public companies with covered employees is capped at $1,000,000
3. Lobbying expenses always result in 0 deduction regardless of amount

Use the existing ExpenseType and deductibleAmount function definitions.
Provide complete proofs using tactics like unfold, aesop, simp, decide.
```

---

### Section 103 (Tax-Exempt Bonds) - 8/10
**Missing Theorems to Prove**:

1. **Private Loan Threshold Correctness** (§141(c))
   ```lean
   theorem private_loan_threshold_correct (proceeds : Rat) :
     let threshold := min (5000000 : Rat) ((5/100 : Rat) * proceeds)
     (proceeds ≤ 100000000 → threshold = (5/100 : Rat) * proceeds) ∧
     (proceeds > 100000000 → threshold = 5000000)
   ```

2. **Federal Guarantee Exclusion** (§149(b))
   ```lean
   theorem federally_guaranteed_not_exempt (b : Bond) :
     isStateOrLocal b = true →
     b.isFederallyGuaranteed = true →
     isTaxExempt b = false
   ```

3. **Loan Test Edge Case** (Large Bond)
   ```lean
   theorem large_bond_loan_test :
     let b := exampleLargeBondWithLoan
     isPrivateActivityBond b = true ∧
     b.privateLoanFinancingAmount > 5000000
   ```

**Aristotle Prompt**:
```
Generate Lean 4 theorems proving IRC §103 bond exemption properties:
1. The private loan threshold is correctly computed as lesser of $5M or 5% of proceeds
2. Federally guaranteed state/local bonds are NEVER tax-exempt (§149(b))
3. A $200M bond with $6M private loan financing triggers private activity bond status

Use Rat (rational numbers) for currency amounts and Bool for predicates.
Provide complete proofs with by-cases analysis for the min function.
```

---

### Section 32 (EITC) - 7/10
**Missing Theorems to Prove**:

1. **Investment Income Disqualification** (§32(i))
   ```lean
   theorem excess_investment_income_ineligible (tp : TaxpayerProfile) (ty : TaxYear) :
     tp.investment_income > get_investment_income_limit ty →
     is_eligible_individual tp ty = false
   ```

2. **MFS Filing Status Exclusion** (§32(d))
   ```lean
   theorem mfs_always_ineligible (tp : TaxpayerProfile) (ty : TaxYear) :
     tp.filing_status = FilingStatus.MarriedFilingSeparately →
     is_eligible_individual tp ty = false
   ```

3. **Credit Zero When Ineligible**
   ```lean
   theorem ineligible_implies_zero_credit (tp : TaxpayerProfile) (ty : TaxYear) :
     ¬is_eligible_individual tp ty →
     calculate_credit tp ty = 0
   ```

**Aristotle Prompt**:
```
Generate Lean 4 theorems proving IRC §32 EITC eligibility rules:
1. Taxpayers with investment income exceeding year-specific limits are ineligible
2. Married Filing Separately status always results in ineligibility
3. Ineligible taxpayers always receive 0 credit

Use the existing TaxpayerProfile, TaxYear, and is_eligible_individual definitions.
Prove these using case analysis and the Bool properties of the eligibility function.
```

---

### Section 24 (Child Tax Credit) - 7/10
**Missing Theorems to Prove**:

1. **TCJA Parameter Application** (2018-2025)
   ```lean
   theorem tcja_parameters_2018_2025 (ty : TaxYear) :
     ty.year >= 2018 ∧ ty.year <= 2025 →
     let params := get_credit_parameters ty
     params.credit_per_child = 2000 ∧
     params.mfj_threshold = 400000 ∧
     params.max_refundable = 1600
   ```

2. **Pre-TCJA Parameter Application** (Before 2018, After 2025)
   ```lean
   theorem pre_post_tcja_parameters (ty : TaxYear) :
     (ty.year < 2018 ∨ ty.year > 2025) →
     let params := get_credit_parameters ty
     params.credit_per_child = 1000 ∧
     params.mfj_threshold = 110000 ∧
     params.max_refundable = 1000
   ```

3. **Credit Non-Negative Regardless of Year**
   ```lean
   theorem credit_nonneg_all_years (t : Taxpayer) (ty : TaxYear) :
     final_credit t ty >= 0
   ```

**Aristotle Prompt**:
```
Generate Lean 4 theorems proving IRC §24 Child Tax Credit temporal correctness:
1. TCJA parameters ($2000 credit, $400k MFJ threshold, $1600 refundable) apply only for tax years 2018-2025
2. Pre/post-TCJA parameters ($1000 credit, $110k MFJ threshold, $1000 refundable) apply outside TCJA period
3. Final credit is non-negative for all tax years

Use TaxYear structure with year : Nat and h_valid : year >= 1913.
Provide proofs using decide for year comparisons and arithmetic properties.
```

---

## Phase 2: Edge Case Verification (Priority: HIGH)

### General Edge Cases for All Sections

1. **Boundary Value Testing**
   - Exactly at thresholds ($5M loan, $1M compensation, investment income limit)
   - Year boundaries (2017→2018, 2025→2026)
   - Zero values, maximum values

2. **Logical Consistency**
   - No contradictory results for same inputs
   - Monotonicity where expected (more income → less credit)
   - Idempotency where expected (applying twice = applying once)

**Aristotle Prompts** (One per section):
```
Generate Lean 4 theorems testing boundary conditions for IRC §[NUMBER]:
1. Test exact threshold values (e.g., exactly $5M, exactly $1M)
2. Test year boundaries (e.g., Dec 31 2025 vs Jan 1 2026 - if time-sensitive)
3. Test zero and maximum value inputs
4. Prove monotonicity properties where applicable

Provide concrete examples as definitions followed by theorem proofs.
```

---

## Phase 3: Integration Strategy

### Approach A: Append to Existing Files (RECOMMENDED)
**Pros**: All code for a section in one place, easier navigation
**Cons**: Files become longer, potential for merge conflicts

**Implementation**:
1. Run Aristotle prompts to generate theorem files
2. Review generated theorems for correctness
3. Append to existing `.lean` files in a new section:
   ```lean
   /-
   Additional verification theorems generated by Harmonic Aristotle
   Date: 2025-12-12
   Purpose: Formal verification of Dec 12 bug fixes
   -/

   -- [Generated theorems here]
   ```

### Approach B: Separate Verification Modules
**Pros**: Cleaner separation, easier to regenerate
**Cons**: More files to manage, need imports

**Implementation**:
1. Create `src/TaxCode/Verification/` directory
2. Create `Section162_Verification.lean`, etc.
3. Import original sections: `import TaxCode.Section162`
4. Add theorems referencing imported definitions

### Approach C: Property Test Suite (FUTURE)
Create QuickCheck-style property-based tests derived from proofs:
```lean
-- In src/TaxCode/Tests/Section162_Properties.lean
#check govt_fine_always_zero
#eval test_property_random_expenses govt_fine_always_zero 1000
```

**Recommendation**: Start with **Approach A** for immediate verification, migrate to **Approach B** if files exceed 500 lines.

---

## Phase 4: Execution Workflow

### Step-by-Step Process

#### For Each Section (§162, §103, §32, §24):

1. **Read Current Implementation**
   ```bash
   bat src/TaxCode/Section[NUMBER].lean
   ```

2. **Submit Aristotle Prompt**
   - Use the prompts from Phase 1 above
   - Submit via Harmonic Aristotle web interface or API
   - Save output to `tmp/aristotle_section[NUMBER]_verification.lean`

3. **Review Generated Code**
   - Check for compilation errors
   - Verify theorems match intended properties
   - Ensure proofs don't use `sorry` or `admit`

4. **Integrate into Codebase**
   ```bash
   # Append to existing file
   cat tmp/aristotle_section[NUMBER]_verification.lean >> src/TaxCode/Section[NUMBER].lean
   ```

5. **Compile and Test**
   ```bash
   lake build TaxCode.Section[NUMBER]
   ```

6. **Document**
   - Add theorem count to README.md
   - Update FIX_SESSION_DEC12_SUMMARY.md with verification status

7. **Commit**
   ```bash
   git add src/TaxCode/Section[NUMBER].lean
   git commit -m "Add formal verification theorems for §[NUMBER] using Aristotle

   - Added [N] theorems proving correctness of Dec 12 fixes
   - Verified [specific properties]
   - All proofs complete without sorry/admit"
   ```

---

## Phase 5: Priority Order

### Week 1 (IMMEDIATE)
1. **§162 verification** - Highest quality (8/10), most critical (business expenses)
2. **§103 verification** - Highest quality (8/10), complex loan threshold logic

### Week 2 (HIGH)
3. **§32 verification** - Good quality (7/10), complex eligibility rules
4. **§24 verification** - Good quality (7/10), TCJA temporal logic

### Week 3 (MEDIUM)
5. **Edge case testing** - All sections, boundary values
6. **Cross-section consistency** - Ensure Currency, TaxYear, FilingStatus consistent

### Week 4+ (LOWER)
7. **Property-based test generation** - Derive executable tests from theorems
8. **CI/CD integration** - Automated proof checking on PR
9. **Documentation** - Proof summary report for each section

---

## Risk Analysis and Mitigation

### Risk 1: Aristotle Generates Invalid Proofs
**Likelihood**: Medium
**Impact**: High (wasted time, false confidence)
**Mitigation**:
- Always compile with `lake build` before accepting
- Manually review all generated theorems
- Test with `#eval` for concrete examples

### Risk 2: Generated Theorems Don't Match Intent
**Likelihood**: Medium
**Impact**: Medium (need to regenerate)
**Mitigation**:
- Write very specific prompts with examples
- Include expected theorem signatures in prompts
- Review before integration

### Risk 3: Proof Complexity Explosion
**Likelihood**: Low
**Impact**: High (unmaintainable code)
**Mitigation**:
- Start with simple properties
- Use Lean's automation (aesop, simp, decide)
- Break complex proofs into lemmas

### Risk 4: Time Investment Too High
**Likelihood**: Medium
**Impact**: Medium (delayed other work)
**Mitigation**:
- Prioritize Phase 1 only (critical properties)
- Set time budget: 2 hours per section max
- Accept "good enough" rather than perfect

---

## Success Metrics

### Quantitative
- [ ] 3+ theorems per section proving critical properties
- [ ] 100% of new logic paths covered by theorems
- [ ] 0 `sorry` or `admit` in final code
- [ ] All code compiles with `lake build`

### Qualitative
- [ ] Increased confidence in fix correctness
- [ ] Documentation of invariants and properties
- [ ] Foundation for future verification work
- [ ] Demonstrates formal methods value to stakeholders

---

## Tools and Resources

### Required
- Harmonic Aristotle access (web interface or API)
- Lean 4.24.0 with Mathlib
- Lake build system
- Text editor with Lean support (VS Code + Lean 4 extension)

### Optional but Helpful
- `lean --server` for interactive proof development
- Aesop documentation for automation tactics
- Mathlib documentation for library theorems

---

## Next Immediate Actions

1. **Start with §162** (highest quality, most critical)
2. **Submit first Aristotle prompt** for govt fine, exec comp, lobbying theorems
3. **Review and integrate** generated code
4. **Test compilation** with `lake build`
5. **Document results** in progress tracking file

---

## Conclusion

This plan provides a **concrete, actionable roadmap** to systematically verify all 4 fixed IRC sections using Harmonic Aristotle. By focusing on **property-based verification** (proving specific correctness properties) rather than full regeneration, we can:

1. **Quickly gain confidence** in the fixes (Phase 1 can be done in 1-2 days)
2. **Build incrementally** from critical properties to edge cases
3. **Maintain existing code** rather than regenerating entire sections
4. **Create lasting value** with theorems that document invariants

The key insight is to **use Aristotle as a theorem generator**, not a full code regenerator, treating it as a specialized tool for formal verification rather than a complete replacement for manual implementation.
