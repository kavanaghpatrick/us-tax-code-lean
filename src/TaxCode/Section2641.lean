/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 918427ae-271a-4e30-88a3-0410001ea3a2
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

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

inductive FilingStatus
  | Single
  | MarriedFilingJointly
  | MarriedFilingSeparately
  | HeadOfHousehold
  | QualifyingWidower
  | Estate
  | Trust
  deriving Repr, DecidableEq, Inhabited

/-!
# IRC Section 2641 - Applicable rate

This file formalizes IRC §2641 (Applicable rate).

## References
- [26 USC §2641](https://www.law.cornell.edu/uscode/text/26/2641)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2641 - Applicable rate
   U.S. Code
   Notes
   prev |
   next
   (a)
   General rule
   For purposes of this chapter, the term “
   applicable rate
   ” means, with respect to any
   generation-skipping transfer
   , the product of—
   (1)
   the
   maximum Federal estate tax rate
   , and
   (2)
   the inclusion ratio with respect to the transfer.
   (b)
   Maximum Federal estate tax rate
   For purposes of subsection (a), the term “
   maximum Federal estate tax rate
   ” means the maximum rate imposed by section 2001 on the estates of decedents dying at the time of the
   taxable distribution,
   taxable termination,
   or
   direct skip,
   as the case may be.
   (Added
   Pub. L. 99–514, title XIV, § 1431(a)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2722
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
   Modification of Generation-Skipping Transfer Tax
   Pub. L. 111–312, title III, § 302(c)
   ,
   Dec. 17, 2010
   ,
   124 Stat. 3302
   , provided that:
   “In the case of any
   generation-skipping transfer
   made after
   December 31, 2009
   , and before
   January 1, 2011
   , the
   applicable rate
   determined under section 2641(a) of the
   Internal Revenue Code of 1986
   shall be zero.”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/