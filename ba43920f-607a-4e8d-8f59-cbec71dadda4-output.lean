/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ba43920f-607a-4e8d-8f59-cbec71dadda4
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

-- Common definitions for US Tax Code formalization
def Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

inductive FilingStatus
  | Single                         -- IRC §1(c)
  | MarriedFilingJointly          -- IRC §1(a)
  | MarriedFilingSeparately       -- IRC §1(d)
  | HeadOfHousehold               -- IRC §1(b)
  | QualifyingWidower             -- IRC §2(b)
  | Estate                         -- IRC §1(e)(1)
  | Trust                          -- IRC §1(e)(2)
  deriving Repr, DecidableEq, Inhabited

structure Taxpayer where
  id : String
  filingStatus : FilingStatus
  taxYear : TaxYear

/-!
# IRC Section 78 - Gross up for deemed paid foreign tax credit

This file formalizes IRC §78 (Gross up for deemed paid foreign tax credit).

## References
- [26 USC §78](https://www.law.cornell.edu/uscode/text/26/78)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 78 - Gross up for deemed paid foreign tax credit
   U.S. Code
   Notes
   prev
   |
   next
   If a domestic corporation chooses to have the benefits of subpart A of part III of subchapter N (relating to foreign tax credit) for any taxable year, an amount equal to the taxes deemed to be paid by such corporation under subsections (a) and (d) of
   section 960
   (determined without regard to the phrase “90 percent of” in subsection (d)(1) thereof) for such taxable year shall be treated for purposes of this title (other than sections 245 and 245A) as a dividend received by such domestic corporation from the foreign corporation.
   (Added
   Pub. L. 87–834, § 9(b)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 1001
   ; amended
   Pub. L. 94–455, title X, § 1033(b)(1)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1628
   ;
   Pub. L. 115–97, title I, § 14301(c)(1)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2222
   ;
   Pub. L. 119–21, title VII, § 70312(a)(2)
   ,
   July 4, 2025
   ,
   139 Stat. 203
   .)
   Editorial Notes
   Amendments
   2025—
   Pub. L. 119–21
   substituted “subsections (a) and (d)” for “subsections (a), (b), and (d)” and “90 percent” for “80 percent”.
   2017—
   Pub. L. 115–97
   amended section generally. Prior to amendment, text read as follows: “If a domestic corporation chooses to have the benefits of subpart A of part III of subchapter N (relating to foreign tax credit) for any taxable year, an amount equal to the taxes deemed to be paid by such corporation under section 902(a) (relating to credit for corporate stockholder in foreign corporation) or under section 960(a)(1) (relating to taxes paid by foreign corporation) for such taxable year shall be treated for purposes of this title (other than section 245) as a dividend received by such domestic corporation from the foreign corporation.”
   1976—
   Pub. L. 94–455
   substituted “section 902(a)” for “section 902(a)(1)” and “section 960(a)(1)” for “section 960(a)(1)(C)”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 2025 Amendment
   Pub. L. 119–21, title VII, § 70312(c)
   ,
   July 4, 2025
   ,
   139 Stat. 203
   , provided that:
   “(1)
   In general.—
   The amendments made by subsection (a) [amending this section and
   section 960 of this title
   ] shall apply to taxable years beginning after
   December 31, 2025
   .
   “(2)
   Disallowance.—
   The amendment made by subsection (b) [amending
   section 960 of this title
   ] shall apply to foreign income taxes paid or accrued (or deemed paid under section 960(b)(1) of the
   Internal Revenue Code of 1986
   ) with respect to any amount excluded from gross income under section 959(a) of such Code by reason of an inclusion in gross income under section 951A(a) of such Code after
   June 28, 2025
   .”
   Effective Date of 2017 Amendment
   Pub. L. 115–97, title I, § 14301(d)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2225
   , provided that:
   “The amendments made by this section [amending this section and sections
   245
   ,
   535
   ,
   545
   ,
   814
   ,
   865
   ,
   901
   ,
   904
   to
   909
   ,
   958
   to
   960
   ,
   1291
   ,
   1293
   , and
   6038
   of this title and repealing
   section 902 of this title
   ] shall apply to taxable years of foreign corporations beginning after
   December 31, 2017
   , and to taxable years of United States shareholders in which or with which such taxable years of foreign corporations end.”
   Effective Date of 1976 Amendment
   Amendment by
   Pub. L. 94–455
   applicable on different dates depending on the date the distributions were received, see
   section 1033(c) of Pub. L. 94–455
   , set out as a note under
   section 960 of this title
   .
   Effective Date
   Pub. L. 87–834, § 9(e)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 1001
   , provided that:
   “The amendments made by this section [enacting this section and amending sections
   535
   ,
   545
   ,
   861
   ,
   901
   , and
   902
   of this title] shall apply—
   “(1)
   in respect of any distribution received by a domestic corporation after
   December 31, 1964
   , and
   “(2)
   in respect of any distribution received by a domestic corporation before
   January 1, 1965
   , in a taxable year of such corporation beginning after
   December 31, 1962
   , but only to the extent that such distribution is made out of the accumulated profits of a foreign corporation for a taxable year (of such foreign corporation) beginning after
   December 31, 1962
   .
   For purposes of paragraph (2), a distribution made by a foreign corporation out of its profits which are attributable to a distribution received from a foreign subsidiary to which [former] section 902(b) applies shall be treated as made out of the accumulated profits of a foreign corporation for a taxable year beginning before
   January 1, 1963
   , to the extent that such distribution was paid out of the accumulated profits of such foreign subsidiary for a taxable year beginning before
   January 1, 1963
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/