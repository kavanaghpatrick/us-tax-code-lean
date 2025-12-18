/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d17c6dab-d33a-4aef-8c47-fe028711dc1e
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
# IRC Section 2046 - Disclaimers

This file formalizes IRC §2046 (Disclaimers).

## References
- [26 USC §2046](https://www.law.cornell.edu/uscode/text/26/2046)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2046 - Disclaimers
   U.S. Code
   Notes
   prev
   | next
   For provisions relating to the effect of a qualified disclaimer for purposes of this chapter, see section 2518.
   (Added
   Pub. L. 94–455, title XX, § 2009(b)(2)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1893
   , § 2045; renumbered § 2046,
   Pub. L. 97–34, title IV, § 403(d)(3)(A)(i)
   ,
   Aug. 13, 1981
   ,
   95 Stat. 304
   .)
   Statutory Notes and Related Subsidiaries
   Effective Date
   Section applicable to transfers creating an interest in person disclaiming made after
   Dec. 31, 1976
   , see
   section 2009(e)(2) of Pub. L. 94–455
   , set out as a note under
   section 2518 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/