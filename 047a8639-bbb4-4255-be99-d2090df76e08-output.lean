/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 047a8639-bbb4-4255-be99-d2090df76e08
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

-- Common definitions for US Tax Code formalization
def Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

inductive FilingStatus
  | Single                         -- IRC §1(c)
  | MarriedFilingJointly          -- IRC §1(a)
  | MarriedFilingSeparately       -- IRC §1(d)
  | HeadOfHousehold               -- IRC §1(b)
  | QualifyingWidower             -- IRC §2(b)
  | Estate                         -- IRC §1(e)(1)
  | Trust                          -- IRC §1(e)(2)
  deriving Repr, DecidableEq, Inhabited

structure Taxpayer where
  id : String
  filingStatus : FilingStatus
  taxYear : TaxYear

/-!
# IRC Section 84 - Transfer of appreciated property to political organizations

This file formalizes IRC §84 (Transfer of appreciated property to political organizations).

## References
- [26 USC §84](https://www.law.cornell.edu/uscode/text/26/84)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 84 - Transfer of appreciated property to political organizations
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   If—
   (1)
   any person transfers property to a
   political organization
   , and
   (2)
   the fair market value of such property exceeds its adjusted basis,
   then for purposes of this chapter the transferor shall be treated as having sold such property to the
   political organization
   on the date of the transfer, and the transferor shall be treated as having realized an amount equal to the fair market value of such property on such date.
   (b)
   Basis of property
   In the case of a transfer of property to a
   political organization
   to which subsection (a) applies, the basis of such property in the hands of the
   political organization
   shall be the same as it would be in the hands of the transferor, increased by the amount of gain recognized to the transferor by reason of such transfer.
   (c)
   Political organization defined
   For purposes of this section, the term “
   political organization
   ” has the meaning given to such term by section 527(e)(1).
   (Added
   Pub. L. 93–625, § 13(a)(1)
   ,
   Jan. 3, 1975
   ,
   88 Stat. 2120
   ; amended
   Pub. L. 115–141, div. U, title IV, § 401(a)(35)
   ,
   Mar. 23, 2018
   ,
   132 Stat. 1186
   .)
   Editorial Notes
   Amendments
   2018—
   Pub. L. 115–141
   substituted
   “political organizations”
   for
   “political organization”
   in section catchline.
   Statutory Notes and Related Subsidiaries
   Effective Date
   Pub. L. 93–625, § 13(b)
   ,
   Jan. 3, 1975
   ,
   88 Stat. 2121
   , provided that:
   “The amendments made by subsection (a) [enacting this section] shall apply to transfers made after
   May 7, 1974
   , in taxable years ending after such date.”
   Nonrecognition of Gain or Loss Where Organization Sold Contributed Property Before
   August 2, 1973
   Pub. L. 93–625, § 13(c)
   ,
   Jan. 3, 1975
   ,
   88 Stat. 2121
   , provided that in the case of the sale or exchange of property before
   Aug. 2, 1973
   , which was acquired by the exempt
   political organization
   by contribution, no gain or loss shall be recognized by such organization.
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/