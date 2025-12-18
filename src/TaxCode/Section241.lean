/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5fe2a197-1c27-4867-94ca-fe5f2fac4526
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
# IRC Section 241 - Allowance of special deductions

This file formalizes IRC §241 (Allowance of special deductions).

## References
- [26 USC §241](https://www.law.cornell.edu/uscode/text/26/241)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 241 - Allowance of special deductions
   U.S. Code
   prev |
   next
   In addition to the deductions provided in part VI (sec. 161 and following), there shall be allowed as deductions in computing taxable income the items specified in this part.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 72
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/