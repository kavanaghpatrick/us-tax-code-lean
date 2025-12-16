/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: baaaebbe-c299-4e9f-90b9-9b383f6d1d72
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
# IRC Section 176 - Payments with respect to employees of certain foreign corporations

This file formalizes IRC §176 (Payments with respect to employees of certain foreign corporations).

## References
- [26 USC §176](https://www.law.cornell.edu/uscode/text/26/176)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 176 - Payments with respect to employees of certain foreign corporations
   U.S. Code
   prev
   |
   next
   In the case of a domestic corporation, there shall be allowed as a deduction amounts (to the extent not compensated for) paid or incurred pursuant to an agreement entered into under
   section 3121(l)
   with respect to services performed by United States citizens employed by foreign subsidiary corporations. Any reimbursement of any amount previously allowed as a deduction under this section shall be included in gross income for the taxable year in which received.
   (Added Sept. 1, 1954, ch. 1206, title II, § 210(a),
   68 Stat. 1096
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/