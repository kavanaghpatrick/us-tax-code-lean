/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b29b5c43-6821-4b1f-9ac2-7d5d84265917
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
# IRC Section 2517 - Repealed. Pub. L. 99–514, title XVIII, § 1852(e)(2)(A), Oct. 22, 1986, 100 Stat. 2868]

This file formalizes IRC §2517 (Repealed. Pub. L. 99–514, title XVIII, § 1852(e)(2)(A), Oct. 22, 1986, 100 Stat. 2868]).

## References
- [26 USC §2517](https://www.law.cornell.edu/uscode/text/26/2517)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2517 - Repealed. Pub. L. 99–514, title XVIII, § 1852(e)(2)(A), Oct. 22, 1986, 100 Stat. 2868]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added and amended
   Pub. L. 85–866, title I
   , §§ 23(f), 68(a),
   Sept. 2, 1958
   ,
   72 Stat. 1623
   , 1659;
   Pub. L. 87–792, § 7(j)
   ,
   Oct. 10, 1962
   ,
   76 Stat. 830
   ;
   Mar. 8, 1966
   ,
   Pub. L. 89–365, § 2(b)
   ,
   80 Stat. 33
   ;
   Dec. 30, 1969
   ,
   Pub. L. 91–172, title I, § 101(j)(24)
   ,
   83 Stat. 528
   ;
   Pub. L. 94–455, title XX, § 2009(c)
   (4), (5),
   Oct. 4, 1976
   ,
   90 Stat. 1895
   , 1896;
   Pub. L. 97–34, title III, § 311(d)(2)
   ,
   Aug. 13, 1981
   ,
   95 Stat. 280
   ;
   Pub. L. 98–369, div. A, title IV, § 491(d)(35)
   ,
   July 18, 1984
   ,
   98 Stat. 851
   , related to the transfers of certain annuities under qualified plans.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to transfers after
   Oct. 22, 1986
   , see
   section 1852(e)(2)(E) of Pub. L. 99–514
   , set out as an Effective Date of 1986 Amendment note under
   section 406 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/