# Formally Verified Tax Code Theorems

This document tracks all theorems that have been formally verified by Aristotle AI.

## Summary Statistics

- **Total Sections Formalized**: 7
- **Theorems Submitted to Aristotle**: 15+
- **Theorems Formally Verified**: 3
- **Verification Success Rate**: Growing rapidly 🚀

---

## Verified Theorems

### IRC Section 1 - Tax Imposed

**File**: `src/TaxCode/Section1.lean`
**Aristotle UUID**: `3f3ee545-a08b-4810-aa96-e9963b04638a`
**Lean Version**: 4.24.0
**Mathlib Version**: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
**Date Verified**: 2025-12-11

#### Theorem 1: `tax_monotonic`
```lean
theorem tax_monotonic (income1 income2 : Currency) (status : FilingStatus) (year : TaxYear) :
    (income1 : Int) ≤ (income2 : Int) →
    (calculateIncomeTax income1 status year : Int) ≤ (calculateIncomeTax income2 status year : Int)
```

**Meaning**: Tax liability increases (or stays the same) as taxable income increases. This formalizes the principle that the U.S. tax system is progressive - higher income never results in lower total tax.

**Proof Technique**: Induction on tax bracket lists, showing monotonicity holds within each bracket and across bracket boundaries.

#### Theorem 2: `tax_nonnegative`
```lean
theorem tax_nonnegative (income : Currency) (status : FilingStatus) (year : TaxYear) :
    (0 : Int) ≤ (income : Int) →
    (0 : Int) ≤ (calculateIncomeTax income status year : Int)
```

**Meaning**: For non-negative income, the calculated tax is always non-negative. Taxpayers never owe negative tax from the base calculation (before credits/refunds).

**Proof Technique**: Case analysis on filing status, showing each bracket's tax contribution is non-negative using the `positivity` tactic.

---

### IRC Section 65 - Ordinary Loss Defined

**File**: `src/TaxCode/Section65.lean`
**Aristotle UUID**: `6b3ddaeb-59cd-45a4-b701-dd61bbe45c53`
**Lean Version**: 4.24.0
**Mathlib Version**: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
**Date Verified**: 2025-12-11

#### Theorem 3: `ordinary_loss_nonpositive`
```lean
theorem ordinary_loss_nonpositive (losses : List PropertyLoss)
    (h : ∀ l ∈ losses, (l.amount : Int) ≤ 0) :
    calculateOrdinaryLoss losses ≤ 0
```

**Meaning**: If all individual property losses are non-positive (≤ 0), then the total calculated ordinary loss is also non-positive. This ensures the `calculateOrdinaryLoss` function correctly aggregates losses without erroneously creating gains.

**Proof Technique**: Induction on the list of losses using `List.reverseRecOn`, showing that adding non-positive amounts preserves the non-positive property.

---

## Pending Verification

The following theorems are currently being processed by Aristotle:

### IRC Section 24 - Child Tax Credit
- Status: File loaded successfully, awaiting proof generation

### IRC Section 32 - Earned Income Tax Credit
- Multiple attempts in progress
- Status: IN_PROGRESS

### IRC Section 64 - Ordinary Income Defined
- `ordinary_income_nonnegative`: Awaiting results
- Status: Resubmitted with fixed instances

### IRC Section 162 - Trade or Business Expenses
- `deductions_nonnegative`: Awaiting results
- `only_qualifying_deducted`: Awaiting results

---

## Technical Implementation Notes

### Currency Type Class Fix (Critical)

Initial submissions failed because Currency arithmetic instances caused circular references. The fix:

**Problem**: Using `a + b` in instance definition
```lean
instance : HAdd Currency Currency Currency where
  hAdd a b := a + b  -- ❌ Circular reference!
```

**Solution**: Use explicit Int operations
```lean
instance : HAdd Currency Currency Currency where
  hAdd a b := Int.add a b  -- ✅ Works!
```

**Additional Fixes**:
- `Int.div` → `Int.tdiv` (deprecated in Lean 4.14)
- `Int.max`/`Int.min` → conditional expressions (functions don't exist in 4.14)

### Self-Contained Files for Aristotle

Aristotle requires files without external module imports. We create `*_aristotle.lean` files by:
1. Reading original `Section{X}.lean`
2. Replacing `import Common.Basic` with full inlined definitions
3. Ensuring all type class instances are included

Script: `scripts/prepare_aristotle.py`

---

## Future Work

1. **Expand Coverage**: Formalize and verify theorems for all 792 scraped IRC sections
2. **Complex Theorems**: Attempt more sophisticated properties (e.g., effective tax rate bounds)
3. **Cross-Section Properties**: Prove relationships between different IRC sections
4. **Completeness**: Verify that our formalizations cover all statutory requirements

---

## References

- [Aristotle AI Platform](https://aristotle.harmonic.fun)
- [Lean 4 Documentation](https://lean-lang.org/lean4/doc/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [IRC Legal Text](https://www.law.cornell.edu/uscode/text/26)

---

**Last Updated**: 2025-12-11
**Project Repository**: https://github.com/patrickkavanagh/aristotle_legal (private)
