/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 21369082-f44d-41f0-b7e6-ef1bbb708665
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
# IRC Section 123 - Amounts received under insurance contracts for certain living expenses

This file formalizes IRC §123 (Amounts received under insurance contracts for certain living expenses).

## References
- [26 USC §123](https://www.law.cornell.edu/uscode/text/26/123)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 123 - Amounts received under insurance contracts for certain living expenses
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   In the case of an individual whose principal residence is damaged or destroyed by fire, storm, or other casualty, or who is denied access to his principal residence by governmental authorities because of the occurrence or threat of occurrence of such a casualty, gross income does not include amounts received by such individual under an insurance contract which are paid to compensate or reimburse such individual for living expenses incurred for himself and members of his household resulting from the loss of use or occupancy of such residence.
   (b)
   Limitation
   Subsection (a) shall apply to amounts received by the taxpayer for living expenses incurred during any period only to the extent the amounts received do not exceed the amount by which—
   (1)
   the actual living expenses incurred during such period for himself and members of his household resulting from the loss of use or occupancy of their residence, exceed
   (2)
   the normal living expenses which would have been incurred for himself and members of his household during such period.
   (Added
   Pub. L. 91–172, title IX, § 901(a)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 709
   .)
   Editorial Notes
   Prior Provisions
   A prior
   section 123
   was renumbered
   section 140 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date
   Pub. L. 91–172, title IX, § 901(c)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 709
   , provided that:
   “The amendments made by this section [enacting this section] shall apply with respect to amounts received on or after
   January 1, 1969
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/