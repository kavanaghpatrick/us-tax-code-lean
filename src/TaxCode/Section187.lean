/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2ba51334-5d55-4390-9872-ebdb36fb055b
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
# IRC Section 187 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(31), Oct. 4, 1976, 90 Stat. 1769]

This file formalizes IRC §187 (Repealed. Pub. L. 94–455, title XIX, § 1901(a)(31), Oct. 4, 1976, 90 Stat. 1769]).

## References
- [26 USC §187](https://www.law.cornell.edu/uscode/text/26/187)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 187 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(31), Oct. 4, 1976, 90 Stat. 1769]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 91–172, title VII, § 707(a)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 674
   ; amended
   Pub. L. 93–625, § 3(d)
   ,
   Jan. 3, 1975
   ,
   88 Stat. 2109
   , provided for an allowance of an amortization deduction for certain coal mine safety equipment, the method of election and termination of such deduction, the definition of term “certified coal mine safety equipment”, and special rules applicable to the amortization deduction.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal effective for taxable years beginning after
   Dec. 31, 1976
   , see
   section 1901(d) of Pub. L. 94–455
   , set out as an Effective Date of 1976 Amendment note under
   section 2 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/