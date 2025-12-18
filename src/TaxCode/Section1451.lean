/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2a2e94d0-08f7-4b31-a701-0082118dd2be
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
# IRC Section 1451 - Repealed. Pub. L. 98–369, div. A, title IV, § 474(r)(29)(A), July 18, 1984, 98 Stat. 844]

This file formalizes IRC §1451 (Repealed. Pub. L. 98–369, div. A, title IV, § 474(r)(29)(A), July 18, 1984, 98 Stat. 844]).

## References
- [26 USC §1451](https://www.law.cornell.edu/uscode/text/26/1451)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1451 - Repealed. Pub. L. 98–369, div. A, title IV, § 474(r)(29)(A), July 18, 1984, 98 Stat. 844]
   U.S. Code
   Notes
   prev |
   next
   Section, acts Aug. 16, 1954, ch. 736,
   68A Stat. 359
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   90 Stat. 1834
   , related to tax-free covenant bonds. The repeal was not applicable with respect to obligations issued before
   Jan. 1, 1984
   , pursuant to
   section 475(b) of Pub. L. 98–369
   , set out as an Effective Date of 1984 Amendment note under
   section 33 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/