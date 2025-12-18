/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 67b2f1d3-d740-4acd-81b8-dceff1f4dc4c
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
# IRC Section 2703 - Certain rights and restrictions disregarded

This file formalizes IRC §2703 (Certain rights and restrictions disregarded).

## References
- [26 USC §2703](https://www.law.cornell.edu/uscode/text/26/2703)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2703 - Certain rights and restrictions disregarded
   U.S. Code
   prev
   |
   next
   (a)
   General rule
   For purposes of this subtitle, the value of any property shall be determined without regard to—
   (1)
   any option, agreement, or other right to acquire or use the property at a price less than the fair market value of the property (without regard to such option, agreement, or right), or
   (2)
   any restriction on the right to sell or use such property.
   (b)
   Exceptions
   Subsection (a) shall not apply to any option, agreement, right, or restriction which meets each of the following requirements:
   (1)
   It is a bona fide business arrangement.
   (2)
   It is not a device to transfer such property to members of the decedent’s family for less than full and adequate consideration in money or money’s worth.
   (3)
   Its terms are comparable to similar arrangements entered into by persons in an arms’ length transaction.
   (Added
   Pub. L. 101–508, title XI, § 11602(a)
   ,
   Nov. 5, 1990
   ,
   104 Stat. 1388–498
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/