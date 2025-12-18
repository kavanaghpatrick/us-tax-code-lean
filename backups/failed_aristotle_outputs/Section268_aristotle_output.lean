/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d151c3b7-0523-41d1-9e53-ab7e58468873
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
# IRC Section 268 - Sale of land with unharvested crop

This file formalizes IRC §268 (Sale of land with unharvested crop).

## References
- [26 USC §268](https://www.law.cornell.edu/uscode/text/26/268)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 268 - Sale of land with unharvested crop
   U.S. Code
   prev
   |
   next
   Where an unharvested crop sold by the taxpayer is considered under the provisions of section 1231 as “property used in the trade or business”, in computing taxable income no deduction (whether or not for the taxable year of the sale and whether for expenses, depreciation, or otherwise) attributable to the production of such crop shall be allowed.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 80
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/