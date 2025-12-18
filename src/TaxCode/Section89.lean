/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b5efd7d9-16d0-4199-9ca1-90b1a298514a
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f0097416-2ce0-48df-bd70-522e5ec4958f
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
# IRC Section 89 - Repealed. Pub. L. 101–140, title II, § 202(a), Nov. 8, 1989, 103 Stat. 830]

This file formalizes IRC §89 (Repealed. Pub. L. 101–140, title II, § 202(a), Nov. 8, 1989, 103 Stat. 830]).

## References
- [26 USC §89](https://www.law.cornell.edu/uscode/text/26/89)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 89 - Repealed. Pub. L. 101–140, title II, § 202(a), Nov. 8, 1989, 103 Stat. 830]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 99–514, title XI, § 1151(a)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2494
   ; amended
   Pub. L. 100–647, title I, § 1011B(a)(1)
   –(9), (21), (28), (29), (34), title III, § 3021(a)(1)(A), (B), (2)(A), (3)–(9), (11)–(13)(A), (b)(2)(B), (3), title VI, § 6051(a),
   Nov. 10, 1988
   ,
   102 Stat. 3483–3485
   , 3487, 3488, 3625–3632, 3695, related to nondiscrimination rules regarding benefits provided under employee benefit plans.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Pub. L. 101–140, title II, § 202(c)
   ,
   Nov. 8, 1989
   ,
   103 Stat. 830
   , provided that:
   “The amendments made by this section [repealing this section] shall take effect as if included in section 1151 of the
   Tax Reform Act of 1986
   [
   Pub. L. 99–514
   , see section 1151(k) set out as a note under
   section 79 of this title
   ].”
   Nonenforcement of Section for Fiscal Year 1990
   Pub. L. 101–136, title V, § 528
   ,
   Nov. 3, 1989
   ,
   103 Stat. 816
   , provided that:
   “No monies appropriated by this Act [see Tables for classification] may be used to implement or enforce section 1151 of the
   Tax Reform Act of 1986
   or the amendments made by such section [
   section 1151 of Pub. L. 99–514
   , which enacted
   section 89 of this title
   , amended sections 79, 105, 106, 117, 120, 125, 127, 129, 132, 414, 505, 3121, 3306, 6039D, and 6652 of this title and
   section 409 of Title 42
   , The Public Health and Welfare, and enacted provisions set out as a note under
   section 89 of this title
   ].”
   Transitional Provisions
   Pub. L. 100–647, title III, § 3021(c)
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3633
   , provided for the first issue of valuation rules, the interim impact on former employees, the meeting of the written requirement for covered plans in connection with implementation of section 89 of the Code, and the issuance by
   Nov. 15, 1988
   , of rules necessary to carry out section 89, prior to repeal by
   Pub. L. 101–140, title II, § 203(a)(7)
   ,
   Nov. 8, 1989
   ,
   103 Stat. 831
   .
   Part-Time Employee Defined for Purposes of Subsection (f)
   Pub. L. 100–647, title VI, § 6070
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3704
   , increased the number of employees who would be excluded from consideration under this section during plan years 1989 and 1990, in the case of a plan maintained by an employer which employs fewer than 10 employees on a normal working day during a plan year, prior to repeal by
   Pub. L. 101–140, title II, § 203(a)(7)
   ,
   Nov. 8, 1989
   ,
   103 Stat. 831
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/