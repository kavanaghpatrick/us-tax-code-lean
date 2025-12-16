/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 77a66fdc-68b0-4016-bc0c-06d3459877c6
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d43be2b9-56b3-4c1d-bfb7-5c72d1d2d681

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
# IRC Section 302 - Distributions in redemption of stock

This file formalizes IRC §302 (Distributions in redemption of stock).

## References
- [26 USC §302](https://www.law.cornell.edu/uscode/text/26/302)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 302 - Distributions in redemption of stock
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   If a corporation redeems its stock (within the meaning of
   section 317(b)
   ), and if paragraph (1), (2), (3), (4), or (5) of subsection (b) applies, such redemption shall be treated as a distribution in part or full payment in exchange for the stock.
   (b)
   Redemptions treated as exchanges
   (1)
   Redemptions not equivalent to dividends
   Subsection (a) shall apply if the redemption is not essentially equivalent to a dividend.
   (2)
  [Legal text truncated for Aristotle submission]
-/