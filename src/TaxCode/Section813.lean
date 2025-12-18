/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0362532c-542c-4836-945b-44af2d5e882e
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
# IRC Section 813 - Repealed. Pub. L. 100–203, title X, § 10242(c)(1), Dec. 22, 1987, 101 Stat. 1330–423]

This file formalizes IRC §813 (Repealed. Pub. L. 100–203, title X, § 10242(c)(1), Dec. 22, 1987, 101 Stat. 1330–423]).

## References
- [26 USC §813](https://www.law.cornell.edu/uscode/text/26/813)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 813 - Repealed. Pub. L. 100–203, title X, § 10242(c)(1), Dec. 22, 1987, 101 Stat. 1330–423]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 98–369, div. A, title II, § 211(a)
   ,
   July 18, 1984
   ,
   98 Stat. 743
   ; amended
   Pub. L. 99–514, title X, § 1011(b)(9)
   , title XVIII, § 1821(j),
   Oct. 22, 1986
   ,
   100 Stat. 2389
   , 2841;
   Pub. L. 100–647, title I, § 1010(a)(1)
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3450
   , related to foreign life insurance companies.
   A prior section 813, act Aug. 16, 1954, ch. 736, § 813, as added Mar. 13, 1956, ch. 83, § 2,
   70 Stat. 46
   , related to adjustment for certain reserves, prior to the general revision of this part by
   Pub. L. 86–69, § 2(a)
   .
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to taxable years beginning after
   Dec. 31, 1987
   , see
   section 10242(d) of Pub. L. 100–203
   , set out as an Effective Date of 1987 Amendment note under
   section 816 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/