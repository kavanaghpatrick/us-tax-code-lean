/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 608723d5-da8a-4243-97b6-d7145cb693a5
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
# IRC Section 1251 - Repealed. Pub. L. 98–369, div. A, title IV, § 492(a), July 18, 1984, 98 Stat. 853]

This file formalizes IRC §1251 (Repealed. Pub. L. 98–369, div. A, title IV, § 492(a), July 18, 1984, 98 Stat. 853]).

## References
- [26 USC §1251](https://www.law.cornell.edu/uscode/text/26/1251)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1251 - Repealed. Pub. L. 98–369, div. A, title IV, § 492(a), July 18, 1984, 98 Stat. 853]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 91–172, title II, § 211(a)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 566
   ; amended
   Pub. L. 92–178, title III, § 305(a)
   ,
   Dec. 10, 1971
   ,
   85 Stat. 524
   ;
   Pub. L. 94–455, title II, § 206(a)
   , (b)(1), (2), title XIV, § 1402(b)(1)(Z), (2), title XIX, §§ 1901(b)(3)(K), 1906(b)(13)(A),
   Oct. 4, 1976
   ,
   90 Stat. 1535
   , 1732, 1793, 1834;
   Pub. L. 97–354, § 5(a)(36)
   ,
   Oct. 19, 1982
   ,
   96 Stat. 1695
   ;
   Pub. L. 98–369, div. A, title X, § 1001(b)(23)
   , (e),
   July 18, 1984
   ,
   98 Stat. 1012
   , related to gain from
   disposition
   of
   property
   used in farming where farm losses offset nonfarm income.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to taxable years beginning after
   Dec. 31, 1983
   , see
   section 492(d) of Pub. L. 98–369
   , set out as an Effective Date of 1984 Amendment note under
   section 170 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/