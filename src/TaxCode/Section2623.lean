/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2e2789e7-e6b4-4399-ab5e-1e1051a433fb
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
# IRC Section 2623 - Taxable amount in case of direct skip

This file formalizes IRC §2623 (Taxable amount in case of direct skip).

## References
- [26 USC §2623](https://www.law.cornell.edu/uscode/text/26/2623)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2623 - Taxable amount in case of direct skip
   U.S. Code
   Notes
   prev
   |
   next
   For purposes of this chapter, the taxable amount in the case of a
   direct skip
   shall be the value of the property received by the trans­feree.
   (Added
   Pub. L. 99–514, title XIV, § 1431(a)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2721
   .)
   Statutory Notes and Related Subsidiaries
   Effective Date
   Section applicable to
   generation-skipping transfers
   (within the meaning of
   section 2611 of this title
   ) made after
   Oct. 22, 1986
   , except as otherwise provided, see
   section 1433 of Pub. L. 99–514
   , set out as a note under
   section 2601 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/