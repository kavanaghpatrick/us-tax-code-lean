/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 57cba319-69b7-420f-9fb6-10bc4a413a16
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
# IRC Section 875 - Partnerships; beneficiaries of estates and trusts

This file formalizes IRC §875 (Partnerships; beneficiaries of estates and trusts).

## References
- [26 USC §875](https://www.law.cornell.edu/uscode/text/26/875)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 875 - Partnerships; beneficiaries of estates and trusts
   U.S. Code
   Notes
   prev
   |
   next
   For purposes of this subtitle—
   (1)
   a nonresident alien individual or foreign corporation shall be considered as being engaged in a trade or business within the United States if the partnership of which such individual or corporation is a member is so engaged, and
   (2)
   a nonresident alien individual or foreign corporation which is a beneficiary of an estate or trust which is engaged in any trade or business within the United States shall be treated as being engaged in such trade or business within the United States.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 281
   ;
   Pub. L. 89–809, title I, § 103(e)(1)
   ,
   Nov. 13, 1966
   ,
   80 Stat. 1551
   .)
   Editorial Notes
   Amendments
   1966—
   Pub. L. 89–809
   designated existing provisions as par. (1), substituted reference to nonresident alien individuals or foreign corporations for reference simply to nonresident alien individuals, and added par. (2).
   Statutory Notes and Related Subsidiaries
   Effective Date of 1966 Amendment
   Amendment by
   Pub. L. 89–809
   applicable with respect to taxable years beginning after
   Dec. 31, 1966
   , see
   section 103(n)(1) of Pub. L. 89–809
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