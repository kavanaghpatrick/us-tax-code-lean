/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 39d6b5c6-fb63-45e9-915f-d7683aecf0ad
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
# IRC Section 27 - Taxes of foreign countries and possessions of the United States

This file formalizes IRC §27 (Taxes of foreign countries and possessions of the United States).

## References
- [26 USC §27](https://www.law.cornell.edu/uscode/text/26/27)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 27 - Taxes of foreign countries and possessions of the United States
   U.S. Code
   Notes
   prev |
   next
   The amount of taxes imposed by foreign countries and possessions of the United States shall be allowed as a credit against the tax imposed by this chapter to the extent provided in
   section 901
   [1]
   (Aug. 16, 1954, ch. 736,
   68A Stat. 13
   , § 33;
   Pub. L. 94–455, title X, § 1051(a)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1643
   ; renumbered § 27,
   Pub. L. 98–369, div. A, title IV, § 471(c)
   ,
   July 18, 1984
   ,
   98 Stat. 826
   ;
   Pub. L. 115–141, div. U, title IV, § 401(d)(1)(A)
   ,
   Mar. 23, 2018
   ,
   132 Stat. 1206
   .)
   [1]
   So in original. Probably should be followed by a period.
   Editorial Notes
   Amendments
   2018—
   Pub. L. 115–141
   amended section generally. Prior to amendment, section consisted of subsecs. (a) and (b) relating to the foreign tax credit under section 901 and the tax credit under section 936, respectively.
   1984—
   Pub. L. 98–369, § 471(c)
   , renumbered
   section 33 of this title
   as this section.
   1976—
   Pub. L. 94–455
   designated existing provisions as subsec. (a) and added subsec. (b).
   Statutory Notes and Related Subsidiaries
   Effective Date of 1976 Amendment
   Pub. L. 94–455, title X, § 1051(i)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1647
   , as amended by
   Pub. L. 99–514, § 2
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2095
   , provided that:
   “(1)
   Except as provided by paragraph (2), the amendments made by this section [enacting
   section 936 of this title
   and amending sections 33 [now 27], 48, 116, 243, 246, 861, 901, 904, 931, 1504, and 6091 of this title] shall apply to taxable years beginning after
   December 31, 1975
   , except that ‘qualified possession source investment income’ as defined in [former] section 936(d)(2) of the
   Internal Revenue Code of 1986
   [formerly I.R.C. 1954] shall include income from any source outside the United States if the taxpayer establishes to the satisfaction of the Secretary of the Treasury or his delegate that the income from such sources was earned before
   October 1, 1976
   .
   “(2)
   The amendment made by subsection (d)(2) [amending
   section 901 of this title
   ] shall not apply to any tax imposed by a possession of the United States with respect to the complete liquidation occurring before
   January 1, 1979
   , of a corporation to the extent that such tax is attributable to earnings and profits accumulated by such corporation during periods ending before
   January 1, 1976
   .”
   Savings Provision
   For provisions that nothing in amendment by
   Pub. L. 115–141
   be construed to affect treatment of certain transactions occurring, property acquired, or items of income, loss, deduction, or credit taken into account prior to
   Mar. 23, 2018
   , for purposes of determining liability for tax for periods ending after
   Mar. 23, 2018
   , see
   section 401(e) of Pub. L. 115–141
   , set out as a note under
   section 23 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/