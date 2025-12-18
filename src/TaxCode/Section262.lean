/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b4cd0879-a15c-4c89-a36d-05dcf4efde95
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
# IRC Section 262 - Personal, living, and family expenses

This file formalizes IRC §262 (Personal, living, and family expenses).

## References
- [26 USC §262](https://www.law.cornell.edu/uscode/text/26/262)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 262 - Personal, living, and family expenses
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   Except as otherwise expressly provided in this chapter, no deduction shall be allowed for personal, living, or family expenses.
   (b)
   Treatment of certain phone expenses
   For purposes of subsection (a), in the case of an individual, any charge (including taxes thereon) for basic local telephone service with respect to the 1st telephone line provided to any residence of the taxpayer shall be treated as a personal expense.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 76
   ;
   Pub. L. 100–647, title V, § 5073(a)
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3682
   .)
   Editorial Notes
   Amendments
   1988—
   Pub. L. 100–647
   amended section generally. Prior to amendment, section read as follows: “Except as otherwise expressly provided in this chapter, no deduction shall be allowed for personal, living, or family expenses.”
   Statutory Notes and Related Subsidiaries
   Effective Date of 1988 Amendment
   Pub. L. 100–647, title V, § 5073(b)
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3682
   , provided that:
   “The amendment made by subsection (a) [amending this section] shall apply to taxable years beginning after
   December 31, 1988
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/