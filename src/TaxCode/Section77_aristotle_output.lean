/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8e5120e6-54b8-48d6-8f4b-61936d790ada
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
# IRC Section 77 - Commodity credit loans

This file formalizes IRC §77 (Commodity credit loans).

## References
- [26 USC §77](https://www.law.cornell.edu/uscode/text/26/77)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 77 - Commodity credit loans
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Election to include loans in income
   Amounts received as loans from the
   Commodity Credit Corporation
   shall, at the election of the taxpayer, be considered as income and shall be included in gross income for the taxable year in which received.
   (b)
   Effect of election on adjustments for subsequent years
   If a taxpayer exercises the election provided for in subsection (a) for any taxable year, then the method of computing income so adopted shall be adhered to with respect to all subsequent taxable years unless with the approval of the Secretary a change to a different method is authorized.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 25
   ;
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1834
   .)
   Editorial Notes
   Amendments
   1976—Subsec. (b).
   Pub. L. 94–455
   struck out “or his delegate” after “Secretary”.
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/