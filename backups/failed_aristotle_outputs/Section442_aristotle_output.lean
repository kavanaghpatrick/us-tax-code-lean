/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6328dd55-ddde-48ab-b658-af25c0cd876b
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
# IRC Section 442 - Change of annual accounting period

This file formalizes IRC §442 (Change of annual accounting period).

## References
- [26 USC §442](https://www.law.cornell.edu/uscode/text/26/442)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 442 - Change of annual accounting period
   U.S. Code
   Notes
   prev
   |
   next
   If a taxpayer changes his
   annual accounting period
   , the new accounting period shall become the taxpayer’s
   taxable year
   only if the change is approved by the Secretary. For purposes of this subtitle, if a taxpayer to whom
   section 441(g)
   applies adopts an
   annual accounting period
   (as defined in section 441(c)) other than a
   calendar year,
   the taxpayer shall be treated as having changed his
   annual accounting period.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 149
   ;
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1834
   .)
   Editorial Notes
   Amendments
   1976—
   Pub. L. 94–455
   struck out “or his delegate” after “Secretary”.
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/