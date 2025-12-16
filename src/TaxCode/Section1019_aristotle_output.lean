/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f8d80d4b-85bc-4967-b6a5-f5e6ba12a0ca
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
# IRC Section 1019 - Property on which lessee has made improvements

This file formalizes IRC §1019 (Property on which lessee has made improvements).

## References
- [26 USC §1019](https://www.law.cornell.edu/uscode/text/26/1019)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1019 - Property on which lessee has made improvements
   U.S. Code
   Notes
   prev
   |
   next
   Neither the basis nor the adjusted basis of any portion of real property shall, in the case of the lessor of such property, be increased or diminished on account of income derived by the lessor in respect of such property and excludable from gross income under section 109 (relating to improvements by lessee on lessor’s property).
   (Aug. 16, 1954, ch. 736,
   68A Stat. 301
   ;
   Pub. L. 113–295, div. A, title II, § 221(a)(76)
   ,
   Dec. 19, 2014
   ,
   128 Stat. 4049
   .)
   Editorial Notes
   Amendments
   2014—
   Pub. L. 113–295
   struck out last sentence which read as follows: “If an amount representing any part of the value of real property attributable to buildings erected or other improvements made by a lessee in respect of such property was included in gross income of the lessor for any taxable year beginning before
   January 1, 1942
   , the basis of each portion of such property shall be properly adjusted for the amount so included in gross income.”
   Statutory Notes and Related Subsidiaries
   Effective Date of 2014 Amendment
   Amendment by
   Pub. L. 113–295
   effective
   Dec. 19, 2014
   , subject to a savings provision, see
   section 221(b) of Pub. L. 113–295
   , set out as a note under
   section 1 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/