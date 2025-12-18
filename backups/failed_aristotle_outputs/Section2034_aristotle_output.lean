/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 372dc0d1-6620-4cc8-ae32-e5ad2053d741
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
# IRC Section 2034 - Dower or curtesy interests

This file formalizes IRC §2034 (Dower or curtesy interests).

## References
- [26 USC §2034](https://www.law.cornell.edu/uscode/text/26/2034)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2034 - Dower or curtesy interests
   U.S. Code
   Notes
   prev
   |
   next
   The value of the gross estate shall include the value of all property to the extent of any interest therein of the surviving spouse, existing at the time of the decedent’s death as dower or curtesy, or by virtue of a statute creating an estate in lieu of dower or curtesy.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 381
   ;
   Pub. L. 87–834, § 18(a)(2)(B)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 1052
   .)
   Editorial Notes
   Amendments
   1962—
   Pub. L. 87–834
   struck out provisions which excepted real property situated outside of the United States.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1962 Amendment
   Amendment by
   Pub. L. 87–834
   applicable to estates of decedents dying after
   Oct. 16, 1962
   , except as otherwise provided, see
   section 18(b) of Pub. L. 87–834
   , set out as a note under
   section 2031 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/