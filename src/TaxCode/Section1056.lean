/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4949f1a9-4745-4426-b24e-19de4d7acf6c
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
# IRC Section 1056 - Repealed. Pub. L. 108–357, title VIII, § 886(b)(1)(A), Oct. 22, 2004, 118 Stat. 1641]

This file formalizes IRC §1056 (Repealed. Pub. L. 108–357, title VIII, § 886(b)(1)(A), Oct. 22, 2004, 118 Stat. 1641]).

## References
- [26 USC §1056](https://www.law.cornell.edu/uscode/text/26/1056)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1056 - Repealed. Pub. L. 108–357, title VIII, § 886(b)(1)(A), Oct. 22, 2004, 118 Stat. 1641]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 94–455, title II, § 212(a)(1)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1545
   ; amended
   Pub. L. 99–514, title VI, § 631(e)(13)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2275
   , related to basis limitation for player contracts transferred in connection with the sale of a franchise.
   A prior
   section 1056
   was renumbered
   section 1063 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to property acquired after
   Oct. 22, 2004
   , see
   section 886(c)(1) of Pub. L. 108–357
   , set out as an Effective Date of 2004 Amendment note under
   section 197 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/