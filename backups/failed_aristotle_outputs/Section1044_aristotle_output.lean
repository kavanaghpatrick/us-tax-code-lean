/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f5d974f7-3ded-4eba-a440-66cda4941411
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
# IRC Section 1044 - Repealed. Pub. L. 115–97, title I, § 13313(a), Dec. 22, 2017, 131 Stat. 2133]

This file formalizes IRC §1044 (Repealed. Pub. L. 115–97, title I, § 13313(a), Dec. 22, 2017, 131 Stat. 2133]).

## References
- [26 USC §1044](https://www.law.cornell.edu/uscode/text/26/1044)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1044 - Repealed. Pub. L. 115–97, title I, § 13313(a), Dec. 22, 2017, 131 Stat. 2133]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 103–66, title XIII, § 13114(a)
   ,
   Aug. 10, 1993
   ,
   107 Stat. 430
   ; amended
   Pub. L. 104–188, title I, § 1703(a)
   ,
   Aug. 20, 1996
   ,
   110 Stat. 1875
   , related to rollover of publicly traded securities gain into specialized small business investment companies.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to sales after
   Dec. 31, 2017
   , see
   section 13313(c) of Pub. L. 115–97
   , set out as an Effective Date of 2017 Amendment note under
   section 1016 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/