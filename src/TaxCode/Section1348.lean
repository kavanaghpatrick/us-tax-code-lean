/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: df2bb817-025d-409f-9086-1f8cbbe6f3b8
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
# IRC Section 1348 - Repealed. Pub. L. 97–34, title I, § 101(c)(1), Aug. 13, 1981, 95 Stat. 183]

This file formalizes IRC §1348 (Repealed. Pub. L. 97–34, title I, § 101(c)(1), Aug. 13, 1981, 95 Stat. 183]).

## References
- [26 USC §1348](https://www.law.cornell.edu/uscode/text/26/1348)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1348 - Repealed. Pub. L. 97–34, title I, § 101(c)(1), Aug. 13, 1981, 95 Stat. 183]
   U.S. Code
   Notes
   prev
   | next
   Section, added
   Pub. L. 91–172, title VIII, § 804(a)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 685
   ; amended
   Pub. L. 93–406, title II, § 2005(c)(14)
   ,
   Sept. 2, 1974
   ,
   88 Stat. 992
   ;
   Pub. L. 94–455, title III, § 302(a)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1554
   ;
   Pub. L. 95–600, title IV
   , §§ 441(a), 442(a), title VII, § 701(x)(1), (2),
   Nov. 6, 1978
   ,
   92 Stat. 2878
   , 2920;
   Pub. L. 95–600, title IV, § 441(a)
   , as amended
   Pub. L. 96–222, title I, § 104(a)(5)(B)
   ,
   Apr. 1, 1980
   ,
   94 Stat. 218
   , provided for a 50-percent maximum rate on personal service income.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal effective for taxable years beginning after
   Dec. 31, 1981
   , see
   section 101(f)(1) of Pub. L. 97–34
   , set out as an Effective Date of 1981 Amendment note under
   section 1 of this title
   .
   Transitional Rule in Case of Taxable Year Beginning Before
   Nov. 1, 1978
   , and Ending After
   Oct. 31, 1978
   Pub. L. 95–600, title IV, § 441(b)(2)
   ,
   Nov. 6, 1978
   ,
   92 Stat. 2878
   , as amended by
   Pub. L. 96–222, title I, § 104(a)(5)(A)
   ,
   Apr. 1, 1980
   ,
   94 Stat. 218
   , provided that in the case of a taxable year which began before
   Nov. 1, 1978
   , and ended after
   Oct. 31, 1978
   , the amount taken into account under subsec. (b)(2)(B) of
   section 1348 of this title
   by reason of
   section 57(a)(9) of this title
   be 50 percent of the lesser of the net capital gain for the taxable year or the net capital gain taking into account only gain or loss properly taken into account for the portion of the taxable year before
   Nov. 1, 1978
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/