/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9ff66c31-bf9e-459f-bb75-9439d8f97ccf
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
# IRC Section 1461 - Liability for withheld tax

This file formalizes IRC §1461 (Liability for withheld tax).

## References
- [26 USC §1461](https://www.law.cornell.edu/uscode/text/26/1461)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1461 - Liability for withheld tax
   U.S. Code
   Notes
   prev
   |
   next
   Every person required to deduct and withhold any tax under this chapter is hereby made liable for such tax and is hereby indemnified against the claims and demands of any person for the amount of any payments made in accordance with the provisions of this chapter.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 360
   ;
   Pub. L. 89–809, title I, § 103(i)
   ,
   Nov. 13, 1966
   ,
   80 Stat. 1554
   .)
   Editorial Notes
   Amendments
   1966—
   Pub. L. 89–809
   struck out requirement that persons required to deduct and withhold any tax under this chapter make return thereof on or before March 15 of each year and pay the tax to the officer designated in section 6151, and substituted “Liability for withheld tax” for “Return and payment of withheld tax” in section catchline.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1966 Amendment
   Amendment by
   Pub. L. 89–809
   applicable with respect to payments occurring after
   Dec. 31, 1966
   , see
   section 103(n)(3) of Pub. L. 89–809
   , set out as a note under
   section 871 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/