/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 66a0dfd7-7163-4179-9376-65faa2252564
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
# IRC Section 1462 - Withheld tax as credit to recipient of income

This file formalizes IRC §1462 (Withheld tax as credit to recipient of income).

## References
- [26 USC §1462](https://www.law.cornell.edu/uscode/text/26/1462)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1462 - Withheld tax as credit to recipient of income
   U.S. Code
   prev
   |
   next
   Income on which any tax is required to be withheld at the source under this chapter shall be included in the return of the recipient of such income, but any amount of tax so withheld shall be credited against the amount of income tax as computed in such return.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 360
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/