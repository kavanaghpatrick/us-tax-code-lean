/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9d66e8bf-48a8-43cc-b998-d6eea69f19a8
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
# IRC Section 180 - Expenditures by farmers for fertilizer, etc.

This file formalizes IRC §180 (Expenditures by farmers for fertilizer, etc.).

## References
- [26 USC §180](https://www.law.cornell.edu/uscode/text/26/180)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 180 - Expenditures by farmers for fertilizer, etc.
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   In general
   A taxpayer engaged in the business of farming may elect to treat as expenses which are not chargeable to capital account expenditures (otherwise chargeable to capital account) which are paid or incurred by him during the taxable year for the purchase or acquisition of fertilizer, lime, ground limestone, marl, or other materials to enrich, neutralize, or condition
   land used in farming
   , or for the application of such materials to such land. The expenditures so treated shall be allowed as a deduction.
   (b)
   Land used in farming
   For purposes of subsection (a), the term “
   land used in farming
   ” means land used (before or simultaneously with the expenditures described in subsection (a)) by the taxpayer or his tenant for the production of crops, fruits, or other agricultural products or for the sustenance of livestock.
   (c)
   Election
   The election under subsection (a) for any taxable year shall be made within the time prescribed by law (including extensions thereof) for filing the return for such taxable year. Such election shall be made in such manner as the Secretary may by regulations prescribe. Such election may not be revoked except with the consent of the Secretary.
   (Added
   Pub. L. 86–779, § 6(a)
   ,
   Sept. 14, 1960
   ,
   74 Stat. 1001
   ; amended
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1834
   .)
   Editorial Notes
   Amendments
   1976—Subsec. (c).
   Pub. L. 94–455
   struck out “or his delegate” after “Secretary”.
   Statutory Notes and Related Subsidiaries
   Effective Date
   Pub. L. 86–779, § 6(d)
   ,
   Sept. 14, 1960
   ,
   74 Stat. 1001
   , provided that:
   “The amendments made by subsections (a), (b), and (c) [enacting this section and amending
   section 263 of this title
   ] shall apply to taxable years beginning after
   December 31, 1959
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/