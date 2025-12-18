/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f2eadd14-f4ab-4dd2-800b-324801110e78
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
# IRC Section 1562 - Repealed. Pub. L. 91–172, title IV, § 401(a)(2), Dec. 30, 1969, 83 Stat. 600]

This file formalizes IRC §1562 (Repealed. Pub. L. 91–172, title IV, § 401(a)(2), Dec. 30, 1969, 83 Stat. 600]).

## References
- [26 USC §1562](https://www.law.cornell.edu/uscode/text/26/1562)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1562 - Repealed. Pub. L. 91–172, title IV, § 401(a)(2), Dec. 30, 1969, 83 Stat. 600]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 88–272, title II, § 235(a)
   ,
   Feb. 26, 1964
   ,
   78 Stat. 117
   , amended
   Pub. L. 91–172, title IV, § 401(b)(2)(A)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 602
   , set limits on the privilege of groups to elect multiple surtax exemptions.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable with respect to taxable years beginning after
   Dec. 31, 1974
   , see
   section 401(h)(1) of Pub. L. 91–172
   , set out as an Effective Date of 1969 Amendment note under
   section 1561 of this title
   .
   Retroactive Termination of Elections
   Pub. L. 91–172, title IV, § 401(g)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 604
   , authorized an affiliated group of corporations making a consolidated return for the taxable year which included
   Dec. 31, 1970
   , to terminate the election under
   section 1562 of this title
   with respect to any prior Dec. 31 which was included in a taxable year of any such corporations from which there was a net operating loss carryover to the 1970 consolidated return year and provided that the termination of such election was to be valid only if in accord with subsecs. (c)(1) and (e) of
   section 1562 of this title
   other than the requirement of making the termination prior to the expiration of the 3 year period specified in subsec. (e) of
   section 1562 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/