/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d9a86707-dd22-4da4-bdba-ce4989d76278
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

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

inductive FilingStatus
  | Single
  | MarriedFilingJointly
  | MarriedFilingSeparately
  | HeadOfHousehold
  | QualifyingWidower
  | Estate
  | Trust
  deriving Repr, DecidableEq, Inhabited

/-!
# IRC Section 1399 - No separate taxable entities for partnerships, corporations, etc.

This file formalizes IRC §1399 (No separate taxable entities for partnerships, corporations, etc.).

## References
- [26 USC §1399](https://www.law.cornell.edu/uscode/text/26/1399)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1399 - No separate taxable entities for partnerships, corporations, etc.
   U.S. Code
   prev
   | next
   Except in any case to which section 1398 applies, no separate taxable entity shall result from the commencement of a case under title 11 of the United States Code.
   (Added
   Pub. L. 96–589, § 3(a)(1)
   ,
   Dec. 24, 1980
   ,
   94 Stat. 3400
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/