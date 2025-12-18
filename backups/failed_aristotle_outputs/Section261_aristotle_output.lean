/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5f840928-773a-4ae0-8fc8-eb17fae82c58
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
# IRC Section 261 - General rule for disallowance of deductions

This file formalizes IRC §261 (General rule for disallowance of deductions).

## References
- [26 USC §261](https://www.law.cornell.edu/uscode/text/26/261)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 261 - General rule for disallowance of deductions
   U.S. Code
   prev |
   next
   In computing taxable income no deduction shall in any case be allowed in respect of the items specified in this part.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 76
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/