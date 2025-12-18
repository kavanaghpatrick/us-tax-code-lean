/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b23e6bc4-fd50-4409-b3e9-5dd15564418e
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
# IRC Section 1018 - Repealed. Pub. L. 96–589, § 6(h)(1), Dec. 24, 1980, 94 Stat. 3410]

This file formalizes IRC §1018 (Repealed. Pub. L. 96–589, § 6(h)(1), Dec. 24, 1980, 94 Stat. 3410]).

## References
- [26 USC §1018](https://www.law.cornell.edu/uscode/text/26/1018)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1018 - Repealed. Pub. L. 96–589, § 6(h)(1), Dec. 24, 1980, 94 Stat. 3410]
   U.S. Code
   Notes
   prev
   |
   next
   Section, acts Aug. 16, 1954, ch. 736,
   68A Stat. 301
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIX, § 1901(a)(124)
   ,
   90 Stat. 1784
   , provided for adjustment of capital structure before
   Sept. 22, 1938
   .
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal effective
   Oct. 1, 1979
   , but not to apply to proceedings under Title 11, Bankruptcy, commenced before
   Oct. 1, 1979
   , see
   section 7(e) of Pub. L. 96–589
   , set out as an Effective Date of 1980 Amendment note under
   section 108 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/