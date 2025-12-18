/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5af1eac7-89ea-44ed-9bf9-0b688eaae9e6
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
# IRC Section 462 - Repealed. June 15, 1955, ch. 143, § 1(b), 69 Stat. 134]

This file formalizes IRC §462 (Repealed. June 15, 1955, ch. 143, § 1(b), 69 Stat. 134]).

## References
- [26 USC §462](https://www.law.cornell.edu/uscode/text/26/462)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 462 - Repealed. June 15, 1955, ch. 143, § 1(b), 69 Stat. 134]
   U.S. Code
   Notes
   prev
   |
   next
   Section, act Aug. 16, 1954, ch. 736
   68A Stat. 158
   , related to reserves for estimated expenses.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal effective with respect to taxable years beginning after
   Dec. 31, 1953
   , and ending after
   Aug. 16, 1954
   , see section 3 of Act
   June 15, 1955
   , set out as an Effective Date of 1955 Amendment note under
   section 381 of this title
   .
   Savings Provision
   For provisions concerning increase in tax in any taxable year ending on or before
   June 15, 1955
   by reason of enactment of act
   June 15, 1955
   , see section 4 of act
   June 15, 1955
   , set out as a note under
   section 381 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/