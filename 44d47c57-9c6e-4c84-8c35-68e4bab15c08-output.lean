/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 44d47c57-9c6e-4c84-8c35-68e4bab15c08
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
# IRC Section 182 - Repealed. Pub. L. 99–514, title IV, § 402(a), Oct. 22, 1986, 100 Stat. 2221]

This file formalizes IRC §182 (Repealed. Pub. L. 99–514, title IV, § 402(a), Oct. 22, 1986, 100 Stat. 2221]).

## References
- [26 USC §182](https://www.law.cornell.edu/uscode/text/26/182)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 182 - Repealed. Pub. L. 99–514, title IV, § 402(a), Oct. 22, 1986, 100 Stat. 2221]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 87–834, § 21(a)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 1063
   ; amended
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1834
   , authorized deduction of expenditures by farmers for clearing land.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Pub. L. 99–514, title IV, § 402(c)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2221
   , provided that:
   “The amendments made by this section [amending sections
   263
   and
   1252
   of this title and repealing this section] shall apply to amounts paid or incurred after
   December 31, 1985
   , in taxable years ending after such date.”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/