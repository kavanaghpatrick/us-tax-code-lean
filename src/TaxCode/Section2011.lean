/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 341a2562-a745-4721-93aa-505ffc9585fa
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
# IRC Section 2011 - Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(95)(A)(i), Dec. 19, 2014, 128 Stat. 4051]

This file formalizes IRC §2011 (Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(95)(A)(i), Dec. 19, 2014, 128 Stat. 4051]).

## References
- [26 USC §2011](https://www.law.cornell.edu/uscode/text/26/2011)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2011 - Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(95)(A)(i), Dec. 19, 2014, 128 Stat. 4051]
   U.S. Code
   Notes
   prev
   |
   next
   Section, act Aug. 16, 1954, ch. 736,
   68A Stat. 374
   ; Feb. 20, 1956, ch. 63, § 3,
   70 Stat. 24
   ;
   Pub. L. 85–866, title I
   , §§ 65(a), 102(c)(1),
   Sept. 2, 1958
   ,
   72 Stat. 1657
   , 1674;
   Pub. L. 86–175, § 3
   ,
   Aug. 21, 1959
   ,
   73 Stat. 397
   ;
   Pub. L. 94–455, title XIX
   , §§ 1902(a)(12)(B), 1906(b)(13)(A), title XX, §§ 2001(c)(1)(A), 2004(f)(3),
   Oct. 4, 1976
   ,
   90 Stat. 1806
   , 1834, 1849, 1872;
   Pub. L. 97–34, title IV, § 422(e)(2)
   ,
   Aug. 13, 1981
   ,
   95 Stat. 316
   ;
   Pub. L. 107–16, title V
   , §§ 531(a), 532(a),
   June 7, 2001
   ,
   115 Stat. 72
   , 73;
   Pub. L. 107–134, title I, § 103(b)(1)
   ,
   Jan. 23, 2002
   ,
   115 Stat. 2431
   , related to credit for
   State death taxes.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal effective
   Dec. 19, 2014
   , subject to a savings provision, see
   section 221(b) of Pub. L. 113–295
   , set out as an Effective Date of 2014 Amendment note under
   section 1 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/