/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bcf4ea39-78e1-4ef0-8edb-83a9a0c48c3e
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
# IRC Section 522 - Repealed. Pub. L. 87–834, § 17(b)(2), Oct. 16, 1962, 76 Stat. 1051]

This file formalizes IRC §522 (Repealed. Pub. L. 87–834, § 17(b)(2), Oct. 16, 1962, 76 Stat. 1051]).

## References
- [26 USC §522](https://www.law.cornell.edu/uscode/text/26/522)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 522 - Repealed. Pub. L. 87–834, § 17(b)(2), Oct. 16, 1962, 76 Stat. 1051]
   U.S. Code
   Notes
   prev
   | next
   Section, act Aug. 16, 1954, ch. 736,
   68A Stat. 177
   , related to tax on farmers’ cooperatives.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable, except as otherwise provided, to taxable years of organizations described in
   section 1381(a) of this title
   beginning after
   Dec. 31, 1962
   , see
   section 17(c) of Pub. L. 87–834
   , set out as an Effective Date note under
   section 1381 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/