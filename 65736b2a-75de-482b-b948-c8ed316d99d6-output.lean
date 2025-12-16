/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 65736b2a-75de-482b-b948-c8ed316d99d6
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
# IRC Section 193 - Tertiary injectants

This file formalizes IRC §193 (Tertiary injectants).

## References
- [26 USC §193](https://www.law.cornell.edu/uscode/text/26/193)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 193 - Tertiary injectants
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Allowance of deduction
   There shall be allowed as a deduction for the taxable year an amount equal to the
   qualified tertiary injectant expenses
   of the taxpayer for tertiary injectants injected during such taxable year.
   (b)
   Qualified tertiary injectant expenses
   For purposes of this section—
   (1)
   In general
   The term “
   qualified tertiary injectant expenses
   ” means any cost paid or incurred (whether or not chargeable to capital account) for any tertiary injectant (other than a
   hydrocarbon injectant
   which is recoverable) which is used as a part of a
   tertiary recovery method.
   (2)
   Hydrocarbon injectant
   The term “
   hydrocarbon injectant
   ” includes natural gas, crude oil, and any other injectant which is comprised of more than an insignificant amount of natural gas or crude oil. The term does not include any tertiary injectant which is hydrocarbon-based, or a hydrocarbon-derivative, and which is comprised of no more than an insignificant amount of natural gas or crude oil. For purposes of this paragraph, that portion of a
   hydrocarbon injectant
   which is not a hydrocarbon shall not be treated as a
   hydrocarbon injectant
   .
   (3)
   Tertiary recovery method
   The term “
   tertiary recovery method
   ” means—
   (A)
   any method which is described in subparagraphs (1) through (9) of section 212.78(c) of the June 1979 energy regulations (as defined by section 4996(b)(8)(C) as in effect before its repeal), or
   (B)
   any other method to provide tertiary enhanced recovery which is approved by the Secretary for purposes of this section.
   (c)
   Application with other deductions
   No deduction shall be allowed under subsection (a) with respect to any expenditure—
   (1)
   with respect to which the taxpayer has made an election under section 263(c), or
   (2)
   with respect to which a deduction is allowed or allowable to the taxpayer under any other provision of this chapter.
   (Added
   Pub. L. 96–223, title II, § 251(a)(1)
   ,
   Apr. 2, 1980
   ,
   94 Stat. 286
   ; amended
   Pub. L. 97–448, title II, § 202(b)
   ,
   Jan. 12, 1983
   ,
   96 Stat. 2396
   ;
   Pub. L. 100–418, title I, § 1941(b)(7)
   ,
   Aug. 23, 1988
   ,
   102 Stat. 1324
   .)
   Editorial Notes
   References in Text
   Section 4996(b)(8)(C), referred to in subsec. (b)(3)(A), was repealed by
   Pub. L. 100–418, title I, § 1941(a)
   ,
   Aug. 23, 1988
   ,
   102 Stat. 1322
   .
   Amendments
   1988—Subsec. (b)(3)(A).
   Pub. L. 100–418
   substituted “section 4996(b)(8)(C) as in effect before its repeal” for “section 4996(b)(8)(C)”.
   1983—Subsec. (b)(1).
   Pub. L. 97–448
   struck out “during the taxable year” after “any cost paid or incurred”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1988 Amendment
   Amendment by
   Pub. L. 100–418
   applicable to crude oil removed from the premises on or after
   Aug. 23, 1988
   , see
   section 1941(c) of Pub. L. 100–418
   , set out as a note under
   section 164 of this title
   .
   Effective Date of 1983 Amendment
   Amendment by
   Pub. L. 97–448
   effective, except as otherwise provided, as if it had been included in the provision of the
   Crude Oil Windfall Profit Tax Act of 1980
   ,
   Pub. L. 96–223
   , to which such amendment relates, see
   section 203(a) of Pub. L. 97–448
   , set out as a note under
   section 6652 of this title
   .
   Effective Date
   Pub. L. 96–223, title II, § 251(b)
   ,
   Apr. 2, 1980
   ,
   94 Stat. 287
   , provided that:
   “The amendments made by this section [enacting this section and amending sections
   263
   ,
   1245
   , and
   1250
   of this title] shall apply to taxable years beginning after
   December 31, 1979
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/