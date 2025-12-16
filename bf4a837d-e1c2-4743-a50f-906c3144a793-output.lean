/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bf4a837d-e1c2-4743-a50f-906c3144a793
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
# IRC Section 161 - Allowance of deductions

This file formalizes IRC §161 (Allowance of deductions).

## References
- [26 USC §161](https://www.law.cornell.edu/uscode/text/26/161)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 161 - Allowance of deductions
   U.S. Code
   Notes
   prev |
   next
   In computing taxable income under section 63, there shall be allowed as deductions the items specified in this part, subject to the exceptions provided in part IX (sec. 261 and following, relating to items not deductible).
   (Aug. 16, 1954, ch. 736,
   68A Stat. 45
   ;
   Pub. L. 95–30, title I, § 102(b)(1)
   ,
   May 23, 1977
   ,
   91 Stat. 137
   .)
   Editorial Notes
   Amendments
   1977—
   Pub. L. 95–30
   substituted “section 63” for “section 63(a)”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1977 Amendment
   Amendment by
   Pub. L. 95–30
   applicable to taxable years beginning after
   Dec. 31, 1976
   , see
   section 106(a) of Pub. L. 95–30
   , set out as a note under
   section 1 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/