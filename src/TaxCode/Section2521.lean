/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f76e1d2d-687e-4ddf-ad17-ca77ac11ea92
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
# IRC Section 2521 - Repealed. Pub. L. 94–455, title XX, § 2001(b)(3), Oct. 4, 1976, 90 Stat. 1849]

This file formalizes IRC §2521 (Repealed. Pub. L. 94–455, title XX, § 2001(b)(3), Oct. 4, 1976, 90 Stat. 1849]).

## References
- [26 USC §2521](https://www.law.cornell.edu/uscode/text/26/2521)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2521 - Repealed. Pub. L. 94–455, title XX, § 2001(b)(3), Oct. 4, 1976, 90 Stat. 1849]
   U.S. Code
   Notes
   prev |
   next
   Section, act Aug. 16, 1954, ch. 736,
   68A Stat. 410
   , allowed a deduction, in the case of a citizen or resident, an exemption of $30,000, less amounts claimed and allowed for calendar year 1932 and calendar years intervening between that year and year for which tax is being computed.
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/