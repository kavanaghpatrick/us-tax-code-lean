/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b06d91b7-b95f-4266-bffb-6d2828951c71
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
# IRC Section 2051 - Definition of taxable estate

This file formalizes IRC §2051 (Definition of taxable estate).

## References
- [26 USC §2051](https://www.law.cornell.edu/uscode/text/26/2051)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2051 - Definition of taxable estate
   U.S. Code
   Notes
   prev |
   next
   For purposes of the tax imposed by section 2001, the value of the taxable estate shall be determined by deducting from the value of the gross estate the deductions provided for in this part.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 388
   ;
   Pub. L. 95–600, title VII, § 702(r)(2)
   ,
   Nov. 6, 1978
   ,
   92 Stat. 2938
   .)
   Editorial Notes
   Amendments
   1978—
   Pub. L. 95–600
   struck out “exemption and” after “gross estate the”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1978 Amendment
   Pub. L. 95–600, title VII, § 702(r)(5)
   ,
   Nov. 6, 1978
   ,
   92 Stat. 2939
   , provided that:
   “The amendments made by this subsection [amending this section and sections
   1016
   ,
   6324B
   , and
   6698A
   of this title] shall apply to estates of decedents dying after
   December 31, 1976
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/