/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2cabc0a4-3a6f-4a30-ade3-1a163909dd17
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
# IRC Section 546 - Income not placed on annual basis

This file formalizes IRC §546 (Income not placed on annual basis).

## References
- [26 USC §546](https://www.law.cornell.edu/uscode/text/26/546)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 546 - Income not placed on annual basis
   U.S. Code
   prev
   |
   next
   Section 443(b) (relating to computation of tax on change of annual accounting period) shall not apply in the computation of the
   personal holding company
   tax imposed by section 541.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 191
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/