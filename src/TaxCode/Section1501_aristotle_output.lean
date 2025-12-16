/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9ef07ee6-ee2d-4f52-a646-916b1ecbf97f
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
# IRC Section 1501 - Privilege to file consolidated returns

This file formalizes IRC §1501 (Privilege to file consolidated returns).

## References
- [26 USC §1501](https://www.law.cornell.edu/uscode/text/26/1501)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1501 - Privilege to file consolidated returns
   U.S. Code
   prev |
   next
   An
   affiliated group
   of corporations shall, subject to the provisions of this chapter, have the privilege of making a consolidated return with respect to the income tax imposed by chapter 1 for the taxable year in lieu of separate returns. The making of a consolidated return shall be upon the condition that all corporations which at any time during the taxable year have been members of the
   affiliated group
   consent to all the consolidated return regulations prescribed under section 1502 prior to the last day prescribed by law for the filing of such return. The making of a consolidated return shall be considered as such consent. In the case of a corporation which is a member of the
   affiliated group
   for a fractional part of the year, the consolidated return shall include the income of such corporation for such part of the year as it is a member of the
   affiliated group
   .
   (Aug. 16, 1954, ch. 736,
   68A Stat. 367
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/