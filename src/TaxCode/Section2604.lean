/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5cbbc670-65bc-4236-b6a3-24322e5564b8
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
# IRC Section 2604 - Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(95)(B)(i), Dec. 19, 2014, 128 Stat. 4051]

This file formalizes IRC §2604 (Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(95)(B)(i), Dec. 19, 2014, 128 Stat. 4051]).

## References
- [26 USC §2604](https://www.law.cornell.edu/uscode/text/26/2604)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2604 - Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(95)(B)(i), Dec. 19, 2014, 128 Stat. 4051]
   U.S. Code
   Notes
   prev
   | next
   Section, added
   Pub. L. 99–514, title XIV, § 1431(a)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2718
   ; amended
   Pub. L. 107–16, title V, § 532(c)(10)
   ,
   June 7, 2001
   ,
   115 Stat. 75
   , related to credit for certain State
   generation-skipping transfer
   taxes.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal effective
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