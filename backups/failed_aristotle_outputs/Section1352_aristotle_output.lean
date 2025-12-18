/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 45a4741a-7cd6-4bbc-ab9f-76f943e58049
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

structure TaxYear where year : Nat

; h_valid : year ≥ 1913; deriving

DecidableEq, Repr
inductive FilingStatus | Single | MarriedFilingJointly | MarriedFilingSeparately | HeadOfHousehold | QualifyingWidower | Estate | Trust deriving Repr, DecidableEq, Inhabited

/-!
# IRC Section 1352 - Alternative tax on qualifying shipping activities

This file formalizes IRC §1352 (Alternative tax on qualifying shipping activities).

## References
- [26 USC §1352](https://www.law.cornell.edu/uscode/text/26/1352)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1352 - Alternative tax on qualifying shipping activities
   U.S. Code
   Notes
   prev |
   next
   In the case of an
   electing corporation
   , the tax imposed by
   section 11
   shall be the amount equal to the sum of—
   (1)
   the tax imposed by
   section 11
   determined after the application of this subchapter, and
   (2)
   a tax equal to—
   (A)
   the highest rate of tax specified in section 11, multiplied by
   (B)
   the notional shipping income for the taxable year.
   (Added
   Pub. L. 108–357, title II, § 248(a)
   ,
   Oct. 22, 2004
   ,
   118 Stat. 1450
   .)
   Statutory Notes and Related Subsidiaries
   Effective Date
   Section applicable to taxable years beginning after
   Oct. 22, 2004
   , see
   section 248(c) of Pub. L. 108–357
   , set out as an Effective Date of 2004 Amendments note under
   section 56 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/