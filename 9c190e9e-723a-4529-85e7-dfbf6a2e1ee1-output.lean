/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9c190e9e-723a-4529-85e7-dfbf6a2e1ee1
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9e8e4eb2-7dfd-43bf-b01e-f1d9e1b6d8cc

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
# IRC Section 170 - Charitable, etc., contributions and gifts

This file formalizes IRC §170 (Charitable, etc., contributions and gifts).

## References
- [26 USC §170](https://www.law.cornell.edu/uscode/text/26/170)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 170 - Charitable, etc., contributions and gifts
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   Allowance of deduction
   (1)
   General rule
   There shall be allowed as a deduction any
   charitable contribution
   (as defined in subsection (c)) payment of which is made within the taxable year. A
   charitable contribution
   shall be allowable as a deduction only if verified under regulations prescribed by the Secretary.
   (2)
  [Legal text truncated for Aristotle submission]
-/