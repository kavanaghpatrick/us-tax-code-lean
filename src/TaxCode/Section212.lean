/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f909a962-7413-48d3-9df7-6a2c128e805f
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token ';'; expected command
unexpected identifier; expected 'instance'-/
set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

def Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

inductive FilingStatus
  | Single
  | MarriedFilingJointly
  | MarriedFilingSeparately
  | HeadOfHousehold
  | QualifyingWidower
  | Estate
  | Trust
  deriving Repr, DecidableEq, Inhabited

/-!
# IRC Section 212 - Expenses for production of income

This file formalizes IRC §212 (Expenses for production of income).

## References
- [26 USC §212](https://www.law.cornell.edu/uscode/text/26/212)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 212 - Expenses for production of income
   U.S. Code
   Notes
   prev
   |
   next
   In the case of an individual, there shall be allowed as a deduction all the ordinary and necessary expenses paid or incurred during the taxable year—
   (1)
   for the production or collection of income;
   (2)
   for the management, conservation, or maintenance of property held for the production of income; or
   (3)
   in connection with the determination, collection, or refund of any tax.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 69
   .)
   Statutory Notes and Related Subsidiaries
   Denial of Deduction for Amounts Paid or Incurred on Judgments in Suits Brought To Recover Price Increases in Purchase of New Principal Residence
   No deductions to be allowed in computing taxable income for two-thirds of any amount paid or incurred on a judgment entered against any person in a suit brought under
   section 208(b) of Pub. L. 94–12
   , see
   section 208(c) of Pub. L. 94–12
   , set out as a note under
   section 44 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/