/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 48dc1db8-7003-4f40-a516-17a28f6640ee
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
# IRC Section 2203 - Definition of executor

This file formalizes IRC §2203 (Definition of executor).

## References
- [26 USC §2203](https://www.law.cornell.edu/uscode/text/26/2203)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2203 - Definition of executor
   U.S. Code
   prev
   |
   next
   The term “
   executor
   ” wherever it is used in this title in connection with the estate tax imposed by this chapter means the
   executor
   or administrator of the decedent, or, if there is no
   executor
   or administrator appointed, qualified, and acting within the United States, then any person in actual or constructive possession of any property of the decedent.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 401
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/