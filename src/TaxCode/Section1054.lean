/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d8c61157-5ec0-4409-9d08-b50acc04a871
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
# IRC Section 1054 - Certain stock of Federal National Mortgage Association

This file formalizes IRC §1054 (Certain stock of Federal National Mortgage Association).

## References
- [26 USC §1054](https://www.law.cornell.edu/uscode/text/26/1054)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1054 - Certain stock of Federal National Mortgage Association
   U.S. Code
   Notes
   prev
   |
   next
   In the case of a share of stock issued pursuant to section 303(c) of the
   Federal National Mortgage Association Charter Act
   (12 U.S.C., sec.
   1718
   ), the basis of such share in the hands of the initial holder shall be an amount equal to the capital contributions evidenced by such share reduced by the amount (if any) required by section 162(d) to be treated (with respect to such share) as ordinary and necessary expenses paid or incurred in carrying on a trade or business.
   (Added
   Pub. L. 86–779, § 8(b)
   ,
   Sept. 14, 1960
   ,
   74 Stat. 1003
   .)
   Editorial Notes
   Prior Provisions
   A prior
   section 1054
   was renumbered
   section 1063 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date
   Section applicable with respect to taxable years beginning after
   Dec. 31, 1959
   , see
   section 8(d) of Pub. L. 86–779
   , set out as an Effective Date of 1960 Amendment note under
   section 162 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/