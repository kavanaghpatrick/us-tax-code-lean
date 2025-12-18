/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d062cebf-7d75-4d53-95cf-463754eb45df
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
# IRC Section 1052 - Basis established by the Revenue Act of 1932 or 1934 or by the Internal Revenue Code of 1939

This file formalizes IRC §1052 (Basis established by the Revenue Act of 1932 or 1934 or by the Internal Revenue Code of 1939).

## References
- [26 USC §1052](https://www.law.cornell.edu/uscode/text/26/1052)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1052 - Basis established by the Revenue Act of 1932 or 1934 or by the Internal Revenue Code of 1939
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Revenue Act of 1932
   If the property was acquired, after
   February 28, 1913
   , in any taxable year beginning before
   January 1, 1934
   , and the basis thereof, for purposes of the
   Revenue Act of 1932
   was prescribed by section 113(a)(6), (7), or (9) of such Act (
   47 Stat. 199
   ), then for purposes of this subtitle the basis shall be the same as the basis therein prescribed in the
   Revenue Act of 1932
   .
   (b)
   Revenue Act of 1934
   If the property was acquired, after
   February 28, 1913
   , in any taxable year beginning before
   January 1, 1936
   , and the basis thereof, for purposes of the
   Revenue Act of 1934
   , was prescribed by section 113(a)(6), (7), or (8) of such Act (
   48 Stat. 706
   ), then for purposes of this subtitle the basis shall be the same as the basis therein prescribed in the
   Revenue Act of 1934
   .
   (c)
   Internal Revenue Code of 1939
   If the property was acquired, after
   February 28, 1913
   , in a transaction to which the
   Internal Revenue Code of 1939
   applied, and the basis thereof, for purposes of the
   Internal Revenue Code of 1939
   , was prescribed by section 113(a)(6), (7), (8), (13), (15), (18), (19), or (23) of such code, then for purposes of this subtitle the basis shall be the same as the basis therein prescribed in the
   Internal Revenue Code of 1939
   .
   (Aug. 16, 1954, ch. 736,
   68A Stat. 310
   .)
   Editorial Notes
   References in Text
   Revenue Act of 1932
   , referred to in section catchline and subsec. (a), is act June 6, 1932, ch. 209,
   47 Stat. 169
   . For complete classification of the Act to the Code, see Tables.
   Revenue Act of 1934
   , referred to in section catchline and subsec. (b), is act May 10, 1934, ch. 277,
   48 Stat. 680
   . For complete classification of this Act to the Code, see Tables.
   The
   Internal Revenue Code of 1939
   , referred to in section catchline and subsec. (c), is act Feb. 10, 1939, ch. 2,
   53 Stat. 1
   . Prior to the enactment of the
   Internal Revenue Code of 1986
   [formerly I.R.C. 1954], the 1939 Code was classified to former Title 26,
   Internal Revenue Code
   . For Table comparisons of the 1939 Code to the 1986 Code, see table I preceding
   section 1 of this title
   .
   Section 113 of the
   Internal Revenue Code of 1939
   , referred to in subsec. (c), was classified to section 113 of former Title 26,
   Internal Revenue Code
   . Section 113 was repealed by
   section 7851(a)(1)(A) of this title
   . For table of comparisons of the 1939 Code to the 1986 Code, see Table I preceding
   section 1 of this title
   . See, also,
   section 7851(e) of this title
   for provision that references in the 1986 Code to a provision of the 1939 Code, not then applicable, shall be deemed a reference to the corresponding provision of the 1986 Code, which is then applicable.
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/