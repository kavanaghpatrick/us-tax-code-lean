/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4bda3532-2028-4450-9376-29ba68ee404c
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
# IRC Section 391 - 26 U.S. Code § 391 to 395 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(55), Oct. 4, 1976, 90 Stat. 1773]

This file formalizes IRC §391 (26 U.S. Code § 391 to 395 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(55), Oct. 4, 1976, 90 Stat. 1773]).

## References
- [26 USC §391](https://www.law.cornell.edu/uscode/text/26/391)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 391 to 395 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(55), Oct. 4, 1976, 90 Stat. 1773]
   U.S. Code
   Notes
   prev
   | next
   Section 391, acts Aug. 16, 1954, ch. 736,
   68A Stat. 131
   ;
   Sept. 2, 1958
   ,
   Pub. L. 85–866, title I, § 22(a)
   ,
   72 Stat. 1620
   , related to effective date of section 301 et seq. of this title.
   Section 392, act Aug. 16, 1954, ch. 736,
   68A Stat. 131
   , related to effective date of section 331 et seq. of this title.
   Section 393, act Aug. 16, 1954, ch. 736,
   68A Stat. 132
   , related to effective date of section 351 et seq. of this title.
   Section 394, act Aug. 16, 1954, ch. 736,
   68A Stat. 133
   , related to effective date of section 381 et seq. of this title.
   Section 395, act Aug. 16, 1954, ch. 736,
   68A Stat. 133
   , related to special rules for application of this subchapter.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal effective for taxable years beginning after
   Dec. 31, 1976
   , see
   section 1901(d) of Pub. L. 94–455
   , set out as an Effective Date of 1976 Amendment note under
   section 2 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/