/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6d90299c-7fea-491f-88ab-72b7c3177f45
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
# IRC Section 266 - Carrying charges

This file formalizes IRC §266 (Carrying charges).

## References
- [26 USC §266](https://www.law.cornell.edu/uscode/text/26/266)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 266 - Carrying charges
   U.S. Code
   Notes
   prev
   |
   next
   No deduction shall be allowed for amounts paid or accrued for such taxes and carrying charges as, under regulations prescribed by the Secretary, are chargeable to capital account with respect to property, if the taxpayer elects, in accordance with such regulations, to treat such taxes or charges as so chargeable.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 78
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