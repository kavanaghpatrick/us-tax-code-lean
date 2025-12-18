/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 53decd90-824c-4f8f-936a-1169a59e5073
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
# IRC Section 1491 - 26 U.S. Code § 1491, 1492 - Repealed. Pub. L. 105–34, title XI, § 1131(a), Aug. 5, 1997, 111 Stat. 978]

This file formalizes IRC §1491 (26 U.S. Code § 1491, 1492 - Repealed. Pub. L. 105–34, title XI, § 1131(a), Aug. 5, 1997, 111 Stat. 978]).

## References
- [26 USC §1491](https://www.law.cornell.edu/uscode/text/26/1491)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1491, 1492 - Repealed. Pub. L. 105–34, title XI, § 1131(a), Aug. 5, 1997, 111 Stat. 978]
   U.S. Code
   Notes
   prev |
   next
   Section 1491, acts Aug. 16, 1954, ch. 736,
   68A Stat. 365
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title X, § 1015(a)
   ,
   90 Stat. 1617
   ;
   Nov. 6, 1978
   ,
   Pub. L. 95–600, title VII, § 701(u)(14)(A)
   ,
   92 Stat. 2919
   ;
   Aug. 20, 1996
   ,
   Pub. L. 104–188, title I, § 1907(b)(1)
   ,
   110 Stat. 1916
   , imposed tax on transfers to avoid income tax.
   Section 1492, acts Aug. 16, 1954, ch. 736,
   68A Stat. 365
   ;
   Jan. 12, 1971
   ,
   Pub. L. 91–681, § 1(b)
   ,
   84 Stat. 2066
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title X, § 1015(b)
   , title XIX, § 1906(b)(13)(A),
   90 Stat. 1618
   , 1834;
   Nov. 6, 1978
   ,
   Pub. L. 95–600, title VII, § 701(u)(14)(B)
   ,
   92 Stat. 2919
   ;
   July 18, 1984
   ,
   Pub. L. 98–369, div. A, title I, § 131(f)(1)
   ,
   98 Stat. 665
   , related to nontaxable transfers.
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/