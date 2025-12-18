/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 04547ea2-9bc4-41d6-9b0d-7935014b4a47
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 73e260fa-e5cc-4dc7-8e89-3ed52c16195b
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
# IRC Section 82 - Reimbursement of moving expenses

This file formalizes IRC §82 (Reimbursement of moving expenses).

## References
- [26 USC §82](https://www.law.cornell.edu/uscode/text/26/82)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 82 - Reimbursement of moving expenses
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   Except as provided in section 132(a)(6), there shall be included in gross income (as compensation for services) any amount received or accrued, directly or indirectly, by an individual as a payment for or reimbursement of expenses of moving from one residence to another residence which is attributable to employment or self-employment.
   (Added
   Pub. L. 91–172, title II, § 231(b)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 579
   ; amended
   Pub. L. 103–66, title XIII, § 13213(d)(3)(A)
   ,
   Aug. 10, 1993
   ,
   107 Stat. 474
   ;
   Pub. L. 115–141, div. U, title IV, § 401(a)(34)
   ,
   Mar. 23, 2018
   ,
   132 Stat. 1186
   .)
   Editorial Notes
   Amendments
   2018—
   Pub. L. 115–141
   substituted “of moving expenses” for “for expenses of moving” in section catchline.
   1993—
   Pub. L. 103–66
   substituted “Except as provided in section 132(a)(6), there shall” for “There shall”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1993 Amendment
   Amendment by
   Pub. L. 103–66
   applicable to reimbursements or other payments in respect of expenses incurred after
   Dec. 31, 1993
   , see
   section 13213(e) of Pub. L. 103–66
   , set out as a note under
   section 62 of this title
   .
   Effective Date
   Section applicable to taxable years beginning after
   December 31, 1969
   , except that it does not apply to moving expenses paid or incurred before
   July 1, 1970
   , in connection with the commencement of work by the taxpayer as an employee at a new principal place of work of which the taxpayer had been notified by his employer on or before
   December 19, 1969
   , see
   section 231(d) of Pub. L. 91–172
   , set out as an Effective Date of 1969 Amendment note under
   section 217 of this title
   .
   Moving Expenses of Members of the Uniformed Services
   Withholding, reporting, inclusion within adjusted gross income, and deduction for reimbursement for moving expenses of members of the uniformed services, see
   section 2 of Pub. L. 93–490
   ,
   Oct. 26, 1974
   ,
   88 Stat. 1466
   , set out as a note under
   section 217 of this title
   .
   CFR Title
   Parts
   26
   301
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/