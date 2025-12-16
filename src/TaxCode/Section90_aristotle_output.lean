/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5bf02fe0-8793-47ad-80b0-c57a3dccc5d0
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
# IRC Section 90 - Illegal Federal irrigation subsidies

This file formalizes IRC §90 (Illegal Federal irrigation subsidies).

## References
- [26 USC §90](https://www.law.cornell.edu/uscode/text/26/90)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 90 - Illegal Federal irrigation subsidies
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   Gross income shall include an amount equal to any
   illegal Federal irrigation subsidy
   received by the taxpayer during the taxable year.
   (b)
   Illegal Federal irrigation subsidy
   For purposes of this section—
   (1)
   In general
   The term “
   illegal Federal irrigation subsidy
   ” means the excess (if any) of—
   (A)
   the amount required to be paid for any
   Federal irrigation water
   delivered to the taxpayer during the taxpayer year, over
   (B)
   the amount paid for such water.
   (2)
   Federal irrigation water
   The term “
   Federal irrigation water
   ” means any water made available for agricultural purposes from the operation of any reclamation or irrigation project referred to in paragraph (8) of section 202 of the
   Reclamation Reform Act of 1982
   .
   (c)
   Denial of deduction
   No deduction shall be allowed under this subtitle by reason of any inclusion in gross income under subsection (a).
   (Added
   Pub. L. 100–203, title X, § 10611(a)
   ,
   Dec. 22, 1987
   ,
   101 Stat. 1330–451
   .)
   Editorial Notes
   References in Text
   Section 202 of the
   Reclamation Reform Act of 1982
   , referred to in subsec. (b)(2), is classified to
   section 390bb of Title 43
   , Public Lands.
   Statutory Notes and Related Subsidiaries
   Effective Date
   Pub. L. 100–203, title X, § 10611(c)
   ,
   Dec. 22, 1987
   ,
   101 Stat. 1330–452
   , provided that:
   “The amendments made by this section [enacting this section] shall apply to water delivered to the taxpayer in months beginning after the date of the enactment of this Act [
   Dec. 22, 1987
   ].”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/