/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: fa2824bf-200b-4255-902d-0ba9ddb500a7
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
# IRC Section 810 - Repealed. Pub. L. 115–97, title I, § 13511(b)(1), Dec. 22, 2017, 131 Stat. 2142]

This file formalizes IRC §810 (Repealed. Pub. L. 115–97, title I, § 13511(b)(1), Dec. 22, 2017, 131 Stat. 2142]).

## References
- [26 USC §810](https://www.law.cornell.edu/uscode/text/26/810)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 810 - Repealed. Pub. L. 115–97, title I, § 13511(b)(1), Dec. 22, 2017, 131 Stat. 2142]
   U.S. Code
   Notes
   prev
   | next
   Section, added
   Pub. L. 98–369, div. A, title II, § 211(a)
   ,
   July 18, 1984
   ,
   98 Stat. 738
   ; amended
   Pub. L. 111–92, § 13(c)
   ,
   Nov. 6, 2009
   ,
   123 Stat. 2994
   ;
   Pub. L. 113–295, div. A, title II, § 221(a)(41)(J)
   ,
   Dec. 19, 2014
   ,
   128 Stat. 4044
   , related to operations loss deduction.
   A prior section 810, added
   Pub. L. 86–69, § 2(a)
   ,
   June 25, 1959
   ,
   73 Stat. 125
   ; amended
   Pub. L. 91–172, title I, § 121(b)(5)(B)
   , title IX, § 907(a)(2),
   Dec. 30, 1969
   ,
   83 Stat. 541
   , 715, related to rules for certain reserves, prior to the general revision of this part by
   Pub. L. 98–369, § 211(a)
   .
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to losses arising in taxable years beginning after
   Dec. 31, 2017
   , see
   section 13511(c) of Pub. L. 115–97
   , set out as an Effective Date of 2017 Amendment note under
   section 381 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/