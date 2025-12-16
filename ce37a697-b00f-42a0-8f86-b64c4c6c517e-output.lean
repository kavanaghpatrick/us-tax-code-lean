/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ce37a697-b00f-42a0-8f86-b64c4c6c517e
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
# IRC Section 2622 - Taxable amount in case of taxable termination

This file formalizes IRC §2622 (Taxable amount in case of taxable termination).

## References
- [26 USC §2622](https://www.law.cornell.edu/uscode/text/26/2622)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2622 - Taxable amount in case of taxable termination
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   In general
   For purposes of this chapter, the taxable amount in the case of a
   taxable termination
   shall be—
   (1)
   the value of all property with respect to which the
   taxable termination
   has occurred, reduced by
   (2)
   any deduction allowed under subsection (b).
   (b)
   Deduction for certain expenses
   For purposes of subsection (a), there shall be allowed a deduction similar to the deduction allowed by section 2053 (relating to expenses, indebtedness, and taxes) for amounts attributable to the property with respect to which the
   taxable termination
   has occurred.
   (Added
   Pub. L. 94–455, title XX, § 2006(a)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1888
   ; amended
   Pub. L. 99–514, title XIV, § 1431(a)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2720
   .)
   Editorial Notes
   Amendments
   1986—
   Pub. L. 99–514
   amended section generally, substituting provisions relating to taxable amount in case of a
   taxable termination
   for former provisions which authorized the Secretary to promulgate regulations. See
   section 2663 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date of 1986 Amendment
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