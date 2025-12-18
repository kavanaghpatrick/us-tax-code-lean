/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 070c21ed-67b3-4db5-befd-b012f6a375da
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
# IRC Section 418 - 26 U.S. Code § 418 to 418D - Repealed. Pub. L. 113–235, div. O, title I, § 108(b)(1), Dec. 16, 2014, 128 Stat. 2787]

This file formalizes IRC §418 (26 U.S. Code § 418 to 418D - Repealed. Pub. L. 113–235, div. O, title I, § 108(b)(1), Dec. 16, 2014, 128 Stat. 2787]).

## References
- [26 USC §418](https://www.law.cornell.edu/uscode/text/26/418)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 418 to 418D - Repealed. Pub. L. 113–235, div. O, title I, § 108(b)(1), Dec. 16, 2014, 128 Stat. 2787]
   U.S. Code
   Notes
   prev |
   next
   Section 418, added
   Pub. L. 96–364, title II, § 202(a)
   ,
   Sept. 26, 1980
   ,
   94 Stat. 1271
   , related to reorganization status.
   Section 418A, added
   Pub. L. 96–364, title II, § 202(a)
   ,
   Sept. 26, 1980
   ,
   94 Stat. 1274
   , related to notice of reorganization and funding requirements.
   Section 418B, added
   Pub. L. 96–364, title II, § 202(a)
   ,
   Sept. 26, 1980
   ,
   94 Stat. 1274
   , related to minimum contribution requirement.
   Section 418C, added
   Pub. L. 96–364, title II, § 202(a)
   ,
   Sept. 26, 1980
   ,
   94 Stat. 1278
   , related to overburden credit against minimum contribution requirement.
   Section 418D, added
   Pub. L. 96–364, title II, § 202(a)
   ,
   Sept. 26, 1980
   ,
   94 Stat. 1280
   , related to adjustments in accrued benefits.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Pub. L. 113–235, div. O, title I, § 108(c)
   ,
   Dec. 16, 2014
   ,
   128 Stat. 2789
   , provided that:
   “The amendments made by this section [amending sections
   418E
   and
   431
   of this title and sections 1084, 1301, and 1426 of Title 29, Labor, and repealing sections
   418
   to
   418D
   of this title and sections 1421 to 1425 of Title 29] shall apply with respect to plan years beginning after
   December 31, 2014
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/