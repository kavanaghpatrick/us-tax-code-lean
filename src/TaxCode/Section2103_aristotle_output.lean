/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5eabacc5-f822-4c52-b315-bdfb2ebdffb0
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
# IRC Section 2103 - Definition of gross estate

This file formalizes IRC §2103 (Definition of gross estate).

## References
- [26 USC §2103](https://www.law.cornell.edu/uscode/text/26/2103)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2103 - Definition of gross estate
   U.S. Code
   prev
   |
   next
   For the purpose of the tax imposed by section 2101, the value of the gross estate of every decedent nonresident not a citizen of the United States shall be that part of his gross estate (determined as provided in
   section 2031
   ) which at the time of his death is situated in the United States.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 397
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/