/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 48cdfc8f-e676-4e07-9baf-6462b52951b6
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
# IRC Section 2524 - Extent of deductions

This file formalizes IRC §2524 (Extent of deductions).

## References
- [26 USC §2524](https://www.law.cornell.edu/uscode/text/26/2524)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2524 - Extent of deductions
   U.S. Code
   prev
   | next
   The deductions provided in sections
   2522
   and
   2523
   shall be allowed only to the extent that the gifts therein specified are included in the amount of gifts against which such deductions are applied.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 414
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/