/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b0a0e7b3-f4da-4363-987b-e003e5bfb4da
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
# IRC Section 2624 - Valuation

This file formalizes IRC §2624 (Valuation).

## References
- [26 USC §2624](https://www.law.cornell.edu/uscode/text/26/2624)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2624 - Valuation
   U.S. Code
   Notes
   prev
   | next
   (a)
   General rule
   Except as otherwise provided in this chapter, property shall be valued as of the time of the
   generation-skipping transfer
   .
   (b)
   Alternate valuation and special use valuation elections apply to certain direct skips
   In the case of any
   direct skip
   of property which is included in the transferor’s gross estate, the value of such property for purposes of this chapter shall be the same as its value for purposes of
   chapter 11
   (determined with regard to sections 2032 and 2032A).
   (c)
   Alternate valuation election permitted in the case of taxable terminations occurring at death
   If 1 or more
   taxable terminations
   with respect to the same trust occur at the same time as and as a result of the death of an individual, an election may be made to value all of the property included in such terminations in accordance with section 2032.
   (d)
   Reduction for consideration provided by trans­feree
   For purposes of this chapter, the value of the property transferred shall be reduced by the amount of any consideration provided by the transferee.
   (Added
   Pub. L. 99–514, title XIV, § 1431(a)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2721
   .)
   Statutory Notes and Related Subsidiaries
   Effective Date
   Section applicable to
   generation-skipping transfers
   (within the meaning of
   section 2611 of this title
   ) made after
   Oct. 22, 1986
   , except as otherwise provided, see
   section 1433 of Pub. L. 99–514
   , set out as a note under
   section 2601 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/