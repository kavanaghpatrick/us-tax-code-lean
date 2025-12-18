/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 86f1617d-6902-432d-b357-9656e2f139be
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
# IRC Section 1444 - Withholding on Virgin Islands source income

This file formalizes IRC §1444 (Withholding on Virgin Islands source income).

## References
- [26 USC §1444](https://www.law.cornell.edu/uscode/text/26/1444)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1444 - Withholding on Virgin Islands source income
   U.S. Code
   Notes
   prev
   |
   next
   For purposes of determining the withholding tax liability incurred in the Virgin Islands pursuant to this title (as made applicable to the Virgin Islands) with respect to amounts received from sources within the Virgin Islands by citizens and resident alien individuals of the United States, and corporations organized in the United States, the rate of withholding tax under sections
   1441
   and
   1442
   on income subject to tax under section 871(a)(1) or 881 shall not exceed the rate of tax on such income under section 871(a)(1) or 881, as the case may be.
   (Added
   Pub. L. 97–455, § 1(b)
   ,
   Jan. 12, 1983
   ,
   96 Stat. 2497
   ; amended
   Pub. L. 100–647, title I, § 1012(x)
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3530
   .)
   Editorial Notes
   Amendments
   1988—
   Pub. L. 100–647
   struck out “(as modified by section 934A)” before “shall not exceed”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1988 Amendment
   Amendment by
   Pub. L. 100–647
   effective, except as otherwise provided, as if included in the provision of the
   Tax Reform Act of 1986
   ,
   Pub. L. 99–514
   , to which such amendment relates, see
   section 1019(a) of Pub. L. 100–647
   , set out as a note under
   section 1 of this title
   .
   Effective Date
   Section applicable to payments made after
   Jan. 12, 1983
   , see
   section 1(e)(2) of Pub. L. 97–455
   , set out as a note under
   section 934 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/