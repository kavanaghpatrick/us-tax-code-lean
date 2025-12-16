/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e0ef707b-f611-46ba-a732-29799eae0fcf
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
# IRC Section 561 - Definition of deduction for dividends paid

This file formalizes IRC §561 (Definition of deduction for dividends paid).

## References
- [26 USC §561](https://www.law.cornell.edu/uscode/text/26/561)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 561 - Definition of deduction for dividends paid
   U.S. Code
   Notes
   prev |
   next
   (a)
   General rule
   The deduction for dividends paid shall be the sum of—
   (1)
   the dividends paid during the taxable year,
   (2)
   the consent dividends for the taxable year (determined under
   section 565
   ), and
   (3)
   in the case of a personal holding company, the dividend carryover described in section 564.
   (b)
   Special rules applicable
   In determining the deduction for dividends paid, the rules provided in section 562 (relating to rules applicable in determining dividends eligible for dividends paid deduction) and section 563 (relating to dividends paid after the close of the taxable year) shall be applicable.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 198
   ;
   Pub. L. 87–403, § 3(f)
   ,
   Feb. 2, 1962
   ,
   76 Stat. 8
   ;
   Pub. L. 94–455, title XIX, § 1901(b)(32)(H)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1800
   .)
   Editorial Notes
   Amendments
   1976—Subsec. (b).
   Pub. L. 94–455
   redesignated existing provisions of par. (1) as subsec. (b) and struck out par. (2) relating to special adjustment on
   disposition
   of antitrust stock as a dividend.
   1962—Subsec. (b).
   Pub. L. 87–403
   designated existing provisions as par. (1) and added par. (2).
   Statutory Notes and Related Subsidiaries
   Effective Date of 1976 Amendment
   Amendment by
   Pub. L. 94–455
   applicable with respect to taxable years beginning after
   Dec. 31, 1976
   , see
   section 1901(d) of Pub. L. 94–455
   , set out as a note under
   section 2 of this title
   .
   Effective Date of 1962 Amendment
   Amendment by
   Pub. L. 87–403
   applicable only with respect to distributions made after
   Feb. 2, 1962
   , see
   section 3(g) of Pub. L. 87–403
   , set out as a note under
   section 312 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/