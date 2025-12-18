/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9c268da3-7dd9-4f7d-acfa-88f507cee127
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
# IRC Section 215 - Repealed. Pub. L. 115–97, title I, § 11051(a), Dec. 22, 2017, 131 Stat. 2089]

This file formalizes IRC §215 (Repealed. Pub. L. 115–97, title I, § 11051(a), Dec. 22, 2017, 131 Stat. 2089]).

## References
- [26 USC §215](https://www.law.cornell.edu/uscode/text/26/215)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 215 - Repealed. Pub. L. 115–97, title I, § 11051(a), Dec. 22, 2017, 131 Stat. 2089]
   U.S. Code
   Notes
   prev
   |
   next
   Section, act Aug. 16, 1954, ch. 736,
   68A Stat. 71
   ;
   Pub. L. 98–369, div. A, title IV, § 422(b)
   ,
   July 18, 1984
   ,
   98 Stat. 797
   , related to a deduction for alimony or separate maintenance payments paid during an individual’s taxable year.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to any divorce or separation instrument (as defined in former
   section 71(b)(2) of this title
   as in effect before
   Dec. 22, 2017
   ) executed after
   Dec. 31, 2018
   , and to such instruments executed on or before
   Dec. 31, 2018
   , and modified after
   Dec. 31, 2018
   , if the modification expressly provides that the amendment made by
   section 11051 of Pub. L. 115–97
   applies to such modification, see
   section 11051(c) of Pub. L. 115–97
   , set out as an Effective Date of 2017 Amendment note under
   section 61 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/