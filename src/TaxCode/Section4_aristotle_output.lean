/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: eba3b3a6-b61a-4211-a210-b748df3b9e63
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
# IRC Section 4 - Repealed. Pub. L. 94–455, title V, § 501(b)(1), Oct. 4, 1976, 90 Stat. 1558]

This file formalizes IRC §4 (Repealed. Pub. L. 94–455, title V, § 501(b)(1), Oct. 4, 1976, 90 Stat. 1558]).

## References
- [26 USC §4](https://www.law.cornell.edu/uscode/text/26/4)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 4 - Repealed. Pub. L. 94–455, title V, § 501(b)(1), Oct. 4, 1976, 90 Stat. 1558]
   U.S. Code
   Notes
   prev
   |
   next
   Section, acts Aug. 16, 1954, ch. 736,
   68A Stat. 10
   ;
   Feb. 26, 1964
   ,
   Pub. L. 88–272, title II, § 232(f)(1)
   , title III, § 301(b)(1), (3),
   78 Stat. 111
   , 140;
   Dec. 30, 1969
   ,
   Pub. L. 91–172, title VIII, § 802(c)(1)
   –(3),
   83 Stat. 677
   , 678;
   Dec. 10, 1971
   ,
   Pub. L. 92–178, title III, § 301(b)
   ,
   85 Stat. 520
   , related to rules for optional tax.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to taxable years beginning after
   Dec. 31, 1975
   , see
   section 508 of Pub. L. 94–455
   , set out as an Effective Date of 1976 Amendment note under
   section 3 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/