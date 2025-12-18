/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cd63199d-3f27-48b3-9db9-53eb6559c677
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
# IRC Section 317 - Other definitions

This file formalizes IRC §317 (Other definitions).

## References
- [26 USC §317](https://www.law.cornell.edu/uscode/text/26/317)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 317 - Other definitions
   U.S. Code
   prev
   |
   next
   (a)
   Property
   For purposes of this part, the term “
   property
   ” means money,
   securities,
   and any other
   property
   ; except that such term does not include stock in the corporation making the distribution (or rights to acquire such stock).
   (b)
   Redemption of stock
   For purposes of this part, stock shall be treated as redeemed by a corporation if the corporation acquires its stock from a shareholder in exchange for
   property
   , whether or not the stock so acquired is cancelled, retired, or held as treasury stock.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 99
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/