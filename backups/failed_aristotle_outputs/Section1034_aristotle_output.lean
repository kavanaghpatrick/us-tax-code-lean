/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e5a07b5a-6568-4963-8c29-eb4af589a1b7
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

structure TaxYear where year : Nat

; h_valid : year ≥ 1913; deriving

DecidableEq, Repr
inductive FilingStatus | Single | MarriedFilingJointly | MarriedFilingSeparately | HeadOfHousehold | QualifyingWidower | Estate | Trust deriving Repr, DecidableEq, Inhabited

/-!
# IRC Section 1034 - Repealed. Pub. L. 105–34, title III, § 312(b), Aug. 5, 1997, 111 Stat. 839]

This file formalizes IRC §1034 (Repealed. Pub. L. 105–34, title III, § 312(b), Aug. 5, 1997, 111 Stat. 839]).

## References
- [26 USC §1034](https://www.law.cornell.edu/uscode/text/26/1034)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1034 - Repealed. Pub. L. 105–34, title III, § 312(b), Aug. 5, 1997, 111 Stat. 839]
   U.S. Code
   Notes
   prev
   |
   next
   Section, acts Aug. 16, 1954, ch. 736,
   68A Stat. 306
   ;
   Sept. 2, 1958
   ,
   Pub. L. 85–866, title I, § 46(b)
   ,
   72 Stat. 1642
   ;
   Feb. 26, 1964
   ,
   Pub. L. 88–272, title II, § 206(b)(4)
   ,
   78 Stat. 40
   ;
   Jan. 2, 1975
   ,
   Pub. L. 93–597, § 6(a)
   ,
   88 Stat. 1953
   ;
   Mar. 29, 1975
   ,
   Pub. L. 94–12, title II, § 207
   ,
   89 Stat. 32
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIX
   , §§ 1901(a)(129), 1906(b)(13)(A),
   90 Stat. 1785
   , 1834;
   May 23, 1977
   ,
   Pub. L. 95–30, title I, § 102(b)(13)
   ,
   91 Stat. 138
   ;
   Nov. 6, 1978
   ,
   Pub. L. 95–600, title IV
   , §§ 404(c)(5), 405(a)–(c)(1),
   92 Stat. 2870
   , 2871;
   Nov. 8, 1978
   ,
   Pub. L. 95–615, title II, § 206
   ,
   92 Stat. 3107
   ;
   Aug. 13, 1981
   ,
   Pub. L. 97–34, title I
   , §§ 112(b)(4), 122(a), (b),
   95 Stat. 195
   , 197;
   July 18, 1984
   ,
   Pub. L. 98–369, div. A, title X, § 1053(a)
   ,
   98 Stat. 1045
   ;
   Oct. 22, 1986
   ,
   Pub. L. 99–514, title XVIII, § 1878(g)
   ,
   100 Stat. 2904
   ;
   Nov. 10, 1988
   ,
   Pub. L. 100–647, title VI, § 6002(a)
   ,
   102 Stat. 3684
   , related to rollover of gain on sale of principal residence.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to sales and exchanges after
   May 6, 1997
   , with certain exceptions, see
   section 312(d) of Pub. L. 105–34
   , set out as an Effective Date of 1997 Amendment note under
   section 121 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/