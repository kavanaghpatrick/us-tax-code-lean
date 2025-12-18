/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9133f5f4-f2d3-476b-9c3e-2cd371d3db75
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 503a37e1-cab5-459c-b86a-92e4991676f2
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token ';'; expected command
unexpected identifier; expected 'instance'-/
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
# IRC Section 109 - Improvements by lessee on lessor’s property

This file formalizes IRC §109 (Improvements by lessee on lessor’s property).

## References
- [26 USC §109](https://www.law.cornell.edu/uscode/text/26/109)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 109 - Improvements by lessee on lessor’s property
   U.S. Code
   prev
   |
   next
   Gross income does not include income (other than rent) derived by a lessor of real property on the termination of a lease, representing the value of such property attributable to buildings erected or other improvements made by the lessee.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 33
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/