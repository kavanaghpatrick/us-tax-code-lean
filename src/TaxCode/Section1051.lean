/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ad1125fc-4e94-4299-9246-25af23ef9e5a
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
# IRC Section 1051 - Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(78), Dec. 19, 2014, 128 Stat. 4049]

This file formalizes IRC §1051 (Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(78), Dec. 19, 2014, 128 Stat. 4049]).

## References
- [26 USC §1051](https://www.law.cornell.edu/uscode/text/26/1051)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1051 - Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(78), Dec. 19, 2014, 128 Stat. 4049]
   U.S. Code
   Notes
   prev |
   next
   Section, Aug. 16, 1954, ch. 736,
   68A Stat. 310
   ;
   Pub. L. 94–455, title XIX
   , §§ 1901(a)(131), 1906(b)(13)(A),
   Oct. 4, 1976
   ,
   90 Stat. 1786
   , 1834, related to property acquired by a corporation during affiliation.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal effective
   Dec. 19, 2014
   , subject to a savings provision, see
   section 221(b) of Pub. L. 113–295
   , set out as an Effective Date of 2014 Amendment note under
   section 1 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/