# Wave 1 - Complete Results

**Updated**: 2025-12-11 18:00 PST
**Status**: ✅ COMPLETE - All submissions processed

---

## Executive Summary

- **Total Sections Submitted**: 20
- **Successfully Loaded**: 7 (skeletons only - no theorems stated)
- **Theorems Proved**: 3 (from 2 sections with actual content)
- **Load Failures**: 13 (placeholder bug - pre-fix submissions)

---

## Proven Theorems ✅

### §1 - Tax Imposed
**UUID**: 3f3ee545-a08b-4810-aa96-e9963b04638a

1. **`tax_monotonic`** - Higher income results in higher tax
   ```lean
   theorem tax_monotonic (income1 income2 : Currency) (status : FilingStatus) (year : TaxYear) :
       (income1 : Int) ≤ (income2 : Int) →
       (calculateIncomeTax income1 status year : Int) ≤ (calculateIncomeTax income2 status year : Int)
   ```

2. **`tax_nonnegative`** - Tax is always non-negative
   ```lean
   theorem tax_nonnegative (income : Currency) (status : FilingStatus) (year : TaxYear) :
       calculateIncomeTax income status year ≥ 0
   ```

### §65 - Ordinary Loss Defined
**UUID**: 6b3ddaeb-59cd-45a4-b701-dd61bbe45c53

3. **`ordinary_loss_nonpositive`** - Losses are non-positive
   ```lean
   theorem ordinary_loss_nonpositive (losses : List PropertyLoss)
       (h : ∀ l ∈ losses, (l.amount : Int) ≤ 0) :
       calculateOrdinaryLoss losses ≤ 0
   ```

**Success Rate**: 100% of sections with stated theorems were proved ✅

---

## Skeleton-Only Submissions (No Theorems) 📄

These loaded successfully but had no theorems to prove:

1. **§151** - Exemptions (UUID: 7b6554ef...)
2. **§152** - Dependents (UUID: dd5fd988...)
3. **§1001** - Determination of gain or loss (UUID: d6f2cea3...)
4. **§1011** - Adjusted basis for gain/loss (UUID: ac1079fd...)
5. **§1012** - Basis of property (cost) (UUID: 1437128f...)
6. **§1221** - Capital asset defined (UUID: 6d506254...)
7. **§1222** - Capital gains/losses terms (UUID: 219bfa09...)

**Status**: Files contain only:
- Currency type definitions (inlined from Common.Basic)
- Tax code text in comments
- `-- TODO: Add theorems to prove`
- `#eval "Section loaded"` (loads successfully but proves nothing)

**Next Action**: Need actual formalization with theorems for these sections

---

## Load Failures - Placeholder Bug ❌

These failed due to `#check placeholder` error (pre-fix submissions):

- §61, §62, §63
- §162, §163, §164, §165, §166, §167, §168, §169, §170

**Error**: `Unknown identifier 'placeholder'`

**Root Cause**: Auto-generated skeletons had `#check placeholder` which doesn't exist in Lean

**Status**: ✅ Bug fixed in skeleton template (changed to `#eval "Section loaded"`)
**Next Action**: Re-prepare and resubmit these 13 sections

---

## Summary Statistics

| Category | Count | Percentage |
|----------|-------|------------|
| Theorems Proved | 3 | N/A |
| Sections with Proofs | 2 | 10% |
| Skeleton-Only (Loaded OK) | 7 | 35% |
| Load Failures (Placeholder) | 13 | 65% |
| **Total Submitted** | **20** | **100%** |

---

## Key Learnings

### ✅ What Worked
1. **Aristotle API** - Reliable, good error messages
2. **Smart Queue** - Successfully managed rate limits
3. **Currency Type** - Fixed instances work perfectly (Int.add, Int.tdiv, conditionals)
4. **Skeleton Fix** - `#eval "Section loaded"` works for loading

### ❌ What Didn't Work
1. **Placeholder Identifier** - `#check placeholder` causes load failure
2. **Empty Skeletons** - Files with no theorems prove nothing (obvious but confirmed)

### 🎯 For Wave 2
1. **Don't submit empty skeletons** - Only submit sections with actual theorems
2. **Verify files locally first** - Run `lean` on them before submitting
3. **Batch similar sections** - Group by tax topic for better organization

---

## Next Steps

### Immediate (This Session)
1. ✅ Download all results (DONE)
2. ✅ Analyze what was proved (DONE)
3. Update PROOFS.md with verified theorems
4. Clean up queue state (smart_queue.json)

### Short-Term (Next Session)
1. Re-prepare the 13 failed sections with placeholder fix
2. Add actual theorems to the 7 skeleton-only sections
3. Submit batch of fixes via smart queue

### Medium-Term (Wave 2 Prep)
1. Formalize 20 more core IRC sections with real theorems
2. Focus on sections with clear mathematical properties
3. Build library of common tax patterns/lemmas

---

## Files Reference

### Result Files (Downloaded)
- §151: `7b6554ef-d0db-4f5e-bf2a-10fe9492fade-output.lean`
- §152: `dd5fd988-eee0-4c15-90a1-8c4ee73f461f-output.lean`
- §1001: `d6f2cea3-ad12-466b-a7ce-0f4458a1b76f-output.lean`
- §1011: `ac1079fd-136f-469c-a8ac-52c727bebcc9-output.lean`
- §1012: `1437128f-d1a9-4ccb-930f-c102a1fe950e-output.lean`
- §1221: `6d506254-943d-4ac6-977b-df688437aa86-output.lean`
- §1222: `219bfa09-3b32-4fbe-8258-74e65caf3331-output.lean`

### Scripts Used
- `scripts/comprehensive_status.py` - API status checker
- `scripts/download_results.py` - Downloads completed results
- `scripts/smart_queue.py` - Rate-limited submission queue

---

**Conclusion**: Wave 1 successfully validated the workflow and infrastructure. Only 2 sections had actual theorems (§1, §65), and Aristotle proved all 3 theorems stated. The infrastructure (API, queue, download scripts) all work perfectly. Next wave should focus on sections with real mathematical content.
