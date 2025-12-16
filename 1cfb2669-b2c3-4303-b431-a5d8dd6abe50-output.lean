/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1cfb2669-b2c3-4303-b431-a5d8dd6abe50
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
# IRC Section 88 - Certain amounts with respect to nuclear decommissioning costs

This file formalizes IRC §88 (Certain amounts with respect to nuclear decommissioning costs).

## References
- [26 USC §88](https://www.law.cornell.edu/uscode/text/26/88)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 88 - Certain amounts with respect to nuclear decommissioning costs
   U.S. Code
   Notes
   prev
   |
   next
   In the case of any taxpayer who is required to include the amount of any nuclear decommissioning costs in the taxpayer’s cost of service for ratemaking purposes, there shall be includible in the gross income of such taxpayer the amount so included for any taxable year.
   (Added
   Pub. L. 98–369, div. A, title I, § 91(f)(1)
   ,
   July 18, 1984
   ,
   98 Stat. 607
   ; amended
   Pub. L. 99–514, title XVIII, § 1807(a)(4)(E)(vii)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2813
   .)
   Editorial Notes
   Amendments
   1986—
   Pub. L. 99–514
   substituted “for ratemaking purposes” for “of ratemaking purposes”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1986 Amendment
   Amendment by
   Pub. L. 99–514
   effective, except as otherwise provided, as if included in the provisions of the
   Tax Reform Act of 1984
   ,
   Pub. L. 98–369, div. A
   , to which such amendment relates, see
   section 1881 of Pub. L. 99–514
   , set out as a note under
   section 48 of this title
   .
   Effective Date
   Section effective
   July 18, 1984
   , with respect to taxable years ending after such date, see
   section 91(g)(5) of Pub. L. 98–369
   , as amended, set out as an Effective Date of 1984 Amendment note under
   section 461 of this title
   .
   Plan Amendments Not Required Until January 1, 1989
   For provisions directing that if any amendments made by subtitle A or subtitle C of title XI [§§
   1101–1147
   and
   1171–1177
   ] or title XVIII [§§ 1800–1899A] of
   Pub. L. 99–514
   require an amendment to any plan, such plan amendment shall not be required to be made before the first plan year beginning on or after
   Jan. 1, 1989
   , see
   section 1140 of Pub. L. 99–514
   , as amended, set out as a note under
   section 401 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/