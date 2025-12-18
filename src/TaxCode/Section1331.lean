/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6fc8c289-fd2f-4656-ac01-20b4c2bec0b4
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
# IRC Section 1331 - 26 U.S. Code § 1331 to 1337 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(145)(A), Oct. 4, 1976, 90 Stat. 1788]

This file formalizes IRC §1331 (26 U.S. Code § 1331 to 1337 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(145)(A), Oct. 4, 1976, 90 Stat. 1788]).

## References
- [26 USC §1331](https://www.law.cornell.edu/uscode/text/26/1331)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1331 to 1337 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(145)(A), Oct. 4, 1976, 90 Stat. 1788]
   U.S. Code
   Notes
   Section 1331, act Aug. 16, 1954, ch. 736,
   68A Stat. 343
   , related to war loss recoveries.
   Section 1332, act Aug. 16, 1954, ch. 736,
   68A Stat. 343
   , related to inclusion in gross income of war loss recoveries.
   Section 1333, act Aug. 16, 1954, ch. 736,
   68A Stat. 344
   , related to tax adjustment measured by prior benefits.
   Section 1334, act Aug. 16, 1954, ch. 736,
   68A Stat. 346
   , related to restoration of value of investments referable to destroyed or seized property.
   Section 1335, act Aug. 16, 1954, ch. 736,
   68A Stat. 346
   , related to election by taxpayer for application of section 1333.
   Section 1336, act Aug. 16, 1954, ch. 736,
   68A Stat. 347
   , related to basis of recovered property.
   Section 1337, act Aug. 16, 1954, ch. 736,
   68A Stat. 347
   , related to applicable rules.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Pub. L. 94–455, title XIX, § 1901(a)(145)(B)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1788
   , provided that:
   “The repeal by subparagraph (A) [repealing sections
   1331
   to
   1337
   of this title] shall apply with respect to war loss recoveries in taxable years beginning after
   December 31, 1976
   ”.
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/