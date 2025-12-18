/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 984b9b97-aa92-4f83-ace3-d04434c5c081
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
# IRC Section 244 - Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(41)(A), Dec. 19, 2014, 128 Stat. 4043]

This file formalizes IRC §244 (Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(41)(A), Dec. 19, 2014, 128 Stat. 4043]).

## References
- [26 USC §244](https://www.law.cornell.edu/uscode/text/26/244)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 244 - Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(41)(A), Dec. 19, 2014, 128 Stat. 4043]
   U.S. Code
   Notes
   prev
   |
   next
   Section, Aug. 16, 1954, ch. 736,
   68A Stat. 73
   ;
   Pub. L. 88–272, title II, § 214(b)(1)
   ,
   Feb. 26, 1964
   ,
   78 Stat. 55
   ;
   Pub. L. 95–600, title III, § 301(b)(3)
   ,
   Nov. 6, 1978
   ,
   92 Stat. 2820
   ;
   Pub. L. 99–514, title VI, § 611(a)(2)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2249
   ;
   Pub. L. 100–203, title X, § 10221(a)(2)
   ,
   Dec. 22, 1987
   ,
   101 Stat. 1330–408
   ;
   Pub. L. 100–647, title II, § 2004(i)(2)
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3603
   , allowed to corporations as a deduction a percentage of the amount received as dividends on the preferred stock of a public utility.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal not applicable to preferred stock issued before
   Oct. 1, 1942
   (determined in the same manner as under
   section 247 of this title
   as in effect before its repeal by
   Pub. L. 113–295
   ), see
   section 221(a)(41)(K) of Pub. L. 113–295
   , set out as an Effective Date of 2014 Amendment note under
   section 172 of this title
   .
   Except as otherwise provided in
   section 221(a) of Pub. L. 113–295
   , repeal effective
   Dec. 19, 2014
   , subject to a savings provision, see
   section 221(b) of Pub. L. 113–295
   , set out as an Effective Date of 2014 Amendment note under
   section 1 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/