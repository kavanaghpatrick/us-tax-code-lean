/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6a68116f-bd63-4630-a5e6-3f80b91bb1de
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
# IRC Section 2054 - Losses

This file formalizes IRC §2054 (Losses).

## References
- [26 USC §2054](https://www.law.cornell.edu/uscode/text/26/2054)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2054 - Losses
   U.S. Code
   prev
   |
   next
   For purposes of the tax imposed by section 2001, the value of the taxable estate shall be determined by deducting from the value of the gross estate losses incurred during the settlement of estates arising from fires, storms, shipwrecks, or other casualties, or from theft, when such losses are not compensated for by insurance or otherwise.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 390
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/