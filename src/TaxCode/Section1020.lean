/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 44556e66-d318-4351-b85c-68aff02b1774
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
# IRC Section 1020 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(125), Oct. 4, 1976, 90 Stat. 1784]

This file formalizes IRC §1020 (Repealed. Pub. L. 94–455, title XIX, § 1901(a)(125), Oct. 4, 1976, 90 Stat. 1784]).

## References
- [26 USC §1020](https://www.law.cornell.edu/uscode/text/26/1020)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1020 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(125), Oct. 4, 1976, 90 Stat. 1784]
   U.S. Code
   Notes
   prev
   |
   next
   Section, act Aug. 16, 1954, ch. 736,
   68A Stat. 302
   , related to election to have
   section 1016(a)(2)(B) of this title
   apply in respect of periods since
   Feb. 28, 1913
   , and before
   Jan. 1, 1952
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/