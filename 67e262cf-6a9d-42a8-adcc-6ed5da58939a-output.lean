/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 67e262cf-6a9d-42a8-adcc-6ed5da58939a
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c6c78978-c39c-4cea-8892-7bda843acad2

Aristotle encountered an error while processing imports for this file.
Error:
unknown module prefix 'Common'

No directory 'Common' or file 'Common.olean' in the search path entries:
/code/harmonic-lean/.lake/packages/batteries/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/Qq/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/aesop/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/proofwidgets/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/importGraph/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/plausible/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/MD4Lean/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/BibtexQuery/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/UnicodeBasic/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/Cli/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/mathlib/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/doc-gen4/.lake/build/lib/lean
/code/harmonic-lean/.lake/build/lib/lean
/root/.elan/toolchains/leanprover--lean4---v4.24.0/lib/lean
/root/.elan/toolchains/leanprover--lean4---v4.24.0/lib/lean

-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token ';'; expected command
unexpected identifier; expected 'instance'-/
set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

def Currency := Int

structure TaxYear where year : Nat

; h_valid : year ≥ 1913; deriving

DecidableEq, Repr
inductive FilingStatus | Single | MarriedFilingJointly | MarriedFilingSeparately | HeadOfHousehold | QualifyingWidower | Estate | Trust deriving Repr, DecidableEq, Inhabited

/-!
# IRC Section 165 - Losses

This file formalizes IRC §165 (Losses).

## References
- [26 USC §165](https://www.law.cornell.edu/uscode/text/26/165)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 165 - Losses
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   General rule
   There shall be allowed as a deduction any loss sustained during the taxable year and not compensated for by insurance or otherwise.
   (b)
   Amount of deduction
   For purposes of subsection (a), the basis for determining the amount of the deduction for any loss shall be the adjusted basis provided in
   section 1011
   for determining the loss from the sale or other
   disposition
   of property.
  [Legal text truncated for Aristotle submission]
-/