/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bc9e1656-5012-464d-96cf-65ce3b82f2ea
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
# IRC Section 1505 - Cross references

This file formalizes IRC §1505 (Cross references).

## References
- [26 USC §1505](https://www.law.cornell.edu/uscode/text/26/1505)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1505 - Cross references
   U.S. Code
   prev
   | next
   (1)
   For suspension of running of statute of limitations when notice in respect of a deficiency is mailed to one corporation, see section 6503(a)(1).
   (2)
   For allocation of income and deductions of related trades or businesses, see section 482.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 370
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/