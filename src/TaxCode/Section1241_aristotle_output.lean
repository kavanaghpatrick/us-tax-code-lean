/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9c9d5705-6a32-40d4-811e-27bb5ecb3edd
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
# IRC Section 1241 - Cancellation of lease or distributor’s agreement

This file formalizes IRC §1241 (Cancellation of lease or distributor’s agreement).

## References
- [26 USC §1241](https://www.law.cornell.edu/uscode/text/26/1241)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1241 - Cancellation of lease or distributor’s agreement
   U.S. Code
   prev
   |
   next
   Amounts received by a lessee for the cancellation of a lease, or by a distributor of goods for the cancellation of a distributor’s agreement (if the distributor has a substantial capital investment in the distributorship), shall be considered as amounts received in exchange for such lease or agreement.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 333
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/