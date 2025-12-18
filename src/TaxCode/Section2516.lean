/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 17ba0a88-8faf-4f60-b1af-c0e31a4ce163
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
# IRC Section 2516 - Certain property settlements

This file formalizes IRC §2516 (Certain property settlements).

## References
- [26 USC §2516](https://www.law.cornell.edu/uscode/text/26/2516)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2516 - Certain property settlements
   U.S. Code
   Notes
   prev
   |
   next
   Where a husband and wife enter into a written agreement relative to their marital and property rights and divorce occurs within the 3-year period beginning on the date 1 year before such agreement is entered into (whether or not such agreement is approved by the divorce decree), any transfers of property or interests in property made pursuant to such agreement—
   (1)
   to either spouse in settlement of his or her marital or property rights, or
   (2)
   to provide a reasonable allowance for the support of issue of the marriage during minority,
   shall be deemed to be transfers made for a full and adequate consideration in money or money’s worth.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 409
   ;
   Pub. L. 98–369, div. A, title IV, § 425(b)
   ,
   July 18, 1984
   ,
   98 Stat. 804
   .)
   Editorial Notes
   Amendments
   1984—
   Pub. L. 98–369
   substituted in introductory text “within the 3-year period beginning on the date 1 year before such agreement is entered into” for “within 2 years thereafter”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1984 Amendment
   Pub. L. 98–369, div. A, title IV, § 425(c)(2)
   ,
   July 18, 1984
   ,
   98 Stat. 804
   , provided that:
   “The amendment made by subsection (b) [amending this section] shall apply to transfers after the date of the enactment of this Act [
   July 18, 1984
   ].”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/