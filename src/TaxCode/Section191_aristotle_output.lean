/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 90e81cf5-692a-4784-81a2-dae551b17bd5
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
# IRC Section 191 - Repealed. Pub. L. 97–34, title II, § 212(d)(1), Aug. 13, 1981, 95 Stat. 239]

This file formalizes IRC §191 (Repealed. Pub. L. 97–34, title II, § 212(d)(1), Aug. 13, 1981, 95 Stat. 239]).

## References
- [26 USC §191](https://www.law.cornell.edu/uscode/text/26/191)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 191 - Repealed. Pub. L. 97–34, title II, § 212(d)(1), Aug. 13, 1981, 95 Stat. 239]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 94–455, title XXI, § 2124(a)(1)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1916
   ; amended
   Pub. L. 95–600, title VII, § 701(f)(1)
   , (2), (7),
   Nov. 6, 1978
   ,
   92 Stat. 2900–2902
   ;
   Pub. L. 96–222, title I, § 107(a)(1)(E)(ii)
   ,
   Apr. 1, 1980
   ,
   94 Stat. 222
   ;
   Pub. L. 96–541, § 2(a)
   ,
   Dec. 17, 1980
   ,
   94 Stat. 3204
   , related to amortization of certain rehabilitation expenditures for certified historic structures.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to expenditures incurred after
   Dec. 31, 1981
   , in taxable years ending after such date, with exceptions, see
   section 212(e) of Pub. L. 97–34
   , set out as an Effective Date of 1981 Amendment note under
   section 46 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/