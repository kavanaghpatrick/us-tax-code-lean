/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c64accda-dbaa-40fd-a030-e33cf34db2e2
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
# IRC Section 81 - Repealed. Pub. L. 100–203, title X, § 10201(b)(1), Dec. 22, 1987, 101 Stat. 1330–387]

This file formalizes IRC §81 (Repealed. Pub. L. 100–203, title X, § 10201(b)(1), Dec. 22, 1987, 101 Stat. 1330–387]).

## References
- [26 USC §81](https://www.law.cornell.edu/uscode/text/26/81)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 81 - Repealed. Pub. L. 100–203, title X, § 10201(b)(1), Dec. 22, 1987, 101 Stat. 1330–387]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 89–722, § 1(b)(1)
   ,
   Nov. 2, 1966
   ,
   80 Stat. 1152
   ; amended
   Pub. L. 93–625, § 4(c)(1)
   ,
   Jan. 3, 1975
   ,
   88 Stat. 2111
   ;
   Pub. L. 94–455, title VI, § 605(b)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1575
   ;
   Pub. L. 99–514, title VIII, § 805(c)(1)(A)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2362
   , included increase in vacation pay suspense account in gross income.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to taxable years beginning after
   Dec. 31, 1987
   , see
   section 10201(c)(1) of Pub. L. 100–203
   , set out as an Effective Date of 1987 Amendment note under
   section 404 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/