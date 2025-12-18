/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e934f66b-2a0d-456d-8859-a1b4ebc0d308
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
# IRC Section 1443 - Foreign tax-exempt organizations

This file formalizes IRC §1443 (Foreign tax-exempt organizations).

## References
- [26 USC §1443](https://www.law.cornell.edu/uscode/text/26/1443)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1443 - Foreign tax-exempt organizations
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   Income subject to section 511
   In the case of income of a foreign organization subject to the tax imposed by section 511, this chapter shall apply to income includible under
   section 512
   in computing its unrelated business taxable income, but only to the extent and subject to such conditions as may be provided under regulations prescribed by the Secretary.
   (b)
   Income subject to section 4948
   In the case of income of a foreign organization subject to the tax imposed by section 4948(a), this chapter shall apply, except that the deduction and withholding shall be at the rate of 4 percent and shall be subject to such conditions as may be provided under regulations prescribed by the Secretary.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 358
   ;
   Pub. L. 91–172, title I
   , §§ 101(j)(22), 121(d)(2)(C),
   Dec. 30, 1969
   ,
   83 Stat. 528
   , 547;
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1834
   .)
   Editorial Notes
   Amendments
   1976—
   Pub. L. 94–455
   struck out “or his delegate” after “Secretary” in two places.
   1969—
   Pub. L. 91–172, § 101(j)(22)
   , designated existing provisions as subsec. (a) and added subsec. (b).
   Subsec. (a).
   Pub. L. 91–172, § 121(d)(2)(C)
   , substituted “income” for “rents” after “this chapter shall apply to”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1969 Amendment
   Amendment by
   section 101(j)(22) of Pub. L. 91–172
   effective
   Jan. 1, 1970
   , see
   section 101(k)(1) of Pub. L. 91–172
   , set out as an Effective Date note under
   section 4940 of this title
   .
   Amendment by
   section 121(d)(2)(C) of Pub. L. 91–172
   applicable to taxable years beginning after
   Dec. 31, 1969
   , see
   section 121(g) of Pub. L. 91–172
   , set out as a note under
   section 511 of this title
   .
   CFR Title
   Parts
   26
   1
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/