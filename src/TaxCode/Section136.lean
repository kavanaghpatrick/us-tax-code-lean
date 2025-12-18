/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 33091961-a2fe-46f7-99a6-bfc0eb6ac842
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 87f47bc1-b9f5-4872-8725-f928d2f837b1
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token ';'; expected command
unexpected identifier; expected 'instance'-/
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
# IRC Section 136 - Energy conservation subsidies provided by public utilities

This file formalizes IRC §136 (Energy conservation subsidies provided by public utilities).

## References
- [26 USC §136](https://www.law.cornell.edu/uscode/text/26/136)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 136 - Energy conservation subsidies provided by public utilities
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Exclusion
   Gross income shall not include the value of any subsidy provided (directly or indirectly) by a
   public utility
   to a customer for the purchase or installation of any
   energy conservation measure
   .
   (b)
   Denial of double benefit
   Notwithstanding any other provision of this subtitle, no deduction or credit shall be allowed for, or by reason of, any expenditure to the extent of the amount excluded under subsection (a) for any subsidy which was provided with respect to such expenditure. The adjusted basis of any property shall be reduced by the amount excluded under subsection (a) which was provided with respect to such property.
   (c)
   Energy conservation measure
   (1)
   In general
   For purposes of this section, the term “
   energy conservation measure
   ” means any installation or modification primarily designed to reduce consumption of electricity or natural gas or to improve the management of energy demand with respect to a
   dwelling unit.
   (2)
   Other definitions
   For purposes of this subsection—
   (A)
   Dwelling unit
   The term “
   dwelling unit
   ” has the meaning given such term by section 280A(f)(1).
   (B)
   Public utility
   The term “
   public utility
   ” means a
   person
   engaged in the sale of electricity or natural gas to residential, commercial, or industrial customers for use by such customers. For purposes of the preceding sentence, the term
   “person”
   includes the Federal Government, a State or local government or any political subdivision thereof, or any instrumentality of any of the foregoing.
   (d)
   Exception
   This section shall not apply to any payment to or from a qualified cogeneration facility or qualifying small power production facility pursuant to section 210 of the
   Public Utility
   Regulatory Policy Act of 1978.
   (Added
   Pub. L. 102–486, title XIX, § 1912(a)
   ,
   Oct. 24, 1992
   ,
   106 Stat. 3014
   ; amended
   Pub. L. 104–188, title I, § 1617(a)
   , (b),
   Aug. 20, 1996
   ,
   110 Stat. 1858
   .)
   Editorial Notes
   References in Text
   Section 210 of the
   Public Utility
   Regulatory Policy Act of 1978, referred to in subsec. (d), probably means section 210 of the
   Public Utility Regulatory Policies Act of 1978
   ,
   Pub. L. 95–617
   , which is classified to
   section 824a–3 of Title 16
   , Conservation.
   Prior Provisions
   A prior
   section 136
   was renumbered
   section 140 of this title
   .
   Amendments
   1996—Subsec. (a).
   Pub. L. 104–188, § 1617(b)(1)
   , reenacted heading without change and amended text generally, substituting present provisions for former provisions which consisted of general exclusion in par. (1) and limitation for exclusion on nonresidential property in par. (2).
   Subsec. (c)(1).
   Pub. L. 104–188, § 1617(a)
   , substituted “energy demand with respect to a
   dwelling unit.
   ” for “energy demand—
   “(A) with respect to a
   dwelling unit
   , and
   “(B) on or after
   January 1, 1995
   , with respect to property other than
   dwelling units.
   The purchase and installation of specially defined energy property shall be treated as an
   energy conservation measure
   described in subparagraph (B).”
   Subsec. (c)(2).
   Pub. L. 104–188, § 1617(b)(2)
   , struck out “and special rules” after “definitions” in heading, redesignated subpars. (B) and (C) as (A) and (B), respectively, and struck out former subpar. (A) which related to “specially defined energy property”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1996 Amendment
   Pub. L. 104–188, title I, § 1617(c)
   ,
   Aug. 20, 1996
   ,
   110 Stat. 1858
   , provided that:
   “The amendments made by this section [amending this section] shall apply to amounts received after
   December 31, 1996
   , unless received pursuant to a written binding contract in effect on
   September 13, 1995
   , and at all times thereafter.”
   Effective Date
   Pub. L. 102–486, title XIX, § 1912(c)
   ,
   Oct. 24, 1992
   ,
   106 Stat. 3016
   , provided that:
   “The amendments made by this section [enacting this section and renumbering former
   section 136
   as 137] shall apply to amounts received after
   December 31, 1992
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/