/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cd27d3d9-21b3-42ed-86ab-9558368df50b
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
# IRC Section 2205 - Reimbursement out of estate

This file formalizes IRC §2205 (Reimbursement out of estate).

## References
- [26 USC §2205](https://www.law.cornell.edu/uscode/text/26/2205)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2205 - Reimbursement out of estate
   U.S. Code
   prev
   |
   next
   If the tax or any part thereof is paid by, or collected out of, that part of the estate passing to or in the possession of any person other than the
   executor
   in his capacity as such, such person shall be entitled to reimbursement out of any part of the estate still undistributed or by a just and equitable contribution by the persons whose interest in the estate of the decedent would have been reduced if the tax had been paid before the distribution of the estate or whose interest is subject to equal or prior liability for the payment of taxes, debts, or other charges against the estate, it being the purpose and intent of this chapter that so far as is practicable and unless otherwise directed by the will of the decedent the tax shall be paid out of the estate before its distribution.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 402
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/