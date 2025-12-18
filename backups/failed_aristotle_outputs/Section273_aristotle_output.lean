/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b582a630-b143-4c1e-9ca1-ba9e007d7a35
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
# IRC Section 273 - Holders of life or terminable interest

This file formalizes IRC §273 (Holders of life or terminable interest).

## References
- [26 USC §273](https://www.law.cornell.edu/uscode/text/26/273)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 273 - Holders of life or terminable interest
   U.S. Code
   Notes
   prev
   |
   next
   Amounts paid under the laws of a State, the District of Columbia, a possession of the United States, or a foreign country as income to the holder of a life or terminable
   interest
   acquired by gift, bequest, or inheritance shall not be reduced or diminished by any deduction for shrinkage (by whatever name called) in the value of such
   interest
   due to the lapse of time.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 83
   ;
   Pub. L. 94–455, title XIX, § 1901(c)(2)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1803
   .)
   Editorial Notes
   Amendments
   1976—
   Pub. L. 94–455
   struck out reference to amounts paid under laws of a Territory.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1976 Amendment
   Amendment by
   Pub. L. 94–455
   effective for taxable years beginning after
   Dec. 31, 1976
   , see
   section 1901(d) of Pub. L. 94–455
   , set out as a note under
   section 2 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/