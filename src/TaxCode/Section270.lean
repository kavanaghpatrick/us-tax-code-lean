/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cd6be861-884c-4372-bc71-9ed5d618aa4f
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
# IRC Section 270 - Repealed. Pub. L. 91–172, title II, § 213(b), Dec. 30, 1969, 83 Stat. 572]

This file formalizes IRC §270 (Repealed. Pub. L. 91–172, title II, § 213(b), Dec. 30, 1969, 83 Stat. 572]).

## References
- [26 USC §270](https://www.law.cornell.edu/uscode/text/26/270)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 270 - Repealed. Pub. L. 91–172, title II, § 213(b), Dec. 30, 1969, 83 Stat. 572]
   U.S. Code
   Notes
   prev
   |
   next
   Section, act Aug. 16, 1954, ch. 736,
   68A Stat. 81
   , related to the limitation on deductions allowable to certain individuals. See
   section 183 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to taxable years beginning after
   Dec. 31, 1969
   , see
   section 213(d) of Pub. L. 91–172
   , set out as an Effective Date note under
   section 183 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/