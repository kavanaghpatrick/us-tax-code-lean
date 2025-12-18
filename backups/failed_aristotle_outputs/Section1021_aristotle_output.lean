/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d49a50d1-df9a-4cdb-81ba-6d4eb6497a79
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
# IRC Section 1021 - Sale of annuities

This file formalizes IRC §1021 (Sale of annuities).

## References
- [26 USC §1021](https://www.law.cornell.edu/uscode/text/26/1021)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1021 - Sale of annuities
   U.S. Code
   prev
   |
   next
   In case of the sale of an annuity contract, the adjusted basis shall in no case be less than zero.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 302
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/