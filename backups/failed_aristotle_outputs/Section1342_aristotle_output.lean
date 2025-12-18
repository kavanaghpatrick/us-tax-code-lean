/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b91499e7-bdd3-4059-b406-3b37940f5c8e
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
# IRC Section 1342 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(147), Oct. 4, 1976, 90 Stat. 1788]

This file formalizes IRC §1342 (Repealed. Pub. L. 94–455, title XIX, § 1901(a)(147), Oct. 4, 1976, 90 Stat. 1788]).

## References
- [26 USC §1342](https://www.law.cornell.edu/uscode/text/26/1342)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1342 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(147), Oct. 4, 1976, 90 Stat. 1788]
   U.S. Code
   Notes
   prev
   | next
   Section, added Aug. 12, 1955, ch. 870, § 3,
   69 Stat. 717
   , related to computation of tax where taxpayer recovers substantial amount held by another under claim of right.
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