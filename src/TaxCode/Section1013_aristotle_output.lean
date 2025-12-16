/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f9eea0e9-f55e-40e2-b59b-f508e2a7509b
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
# IRC Section 1013 - Basis of property included in inventory

This file formalizes IRC §1013 (Basis of property included in inventory).

## References
- [26 USC §1013](https://www.law.cornell.edu/uscode/text/26/1013)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1013 - Basis of property included in inventory
   U.S. Code
   prev
   |
   next
   If the property should have been included in the last inventory, the basis shall be the last inventory value thereof.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 296
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/