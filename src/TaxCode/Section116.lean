/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3ec343eb-e88b-439d-b09d-821ba79f00c2
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 877afc8a-9167-473e-bb79-1f855b1337f6
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
# IRC Section 116 - Repealed. Pub. L. 99–514, title VI, § 612(a), Oct. 22, 1986, 100 Stat. 2250]

This file formalizes IRC §116 (Repealed. Pub. L. 99–514, title VI, § 612(a), Oct. 22, 1986, 100 Stat. 2250]).

## References
- [26 USC §116](https://www.law.cornell.edu/uscode/text/26/116)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 116 - Repealed. Pub. L. 99–514, title VI, § 612(a), Oct. 22, 1986, 100 Stat. 2250]
   U.S. Code
   Notes
   prev
   |
   next
   Section, acts Aug. 16, 1954, ch. 736,
   68A Stat. 37
   ;
   June 25, 1959
   ,
   Pub. L. 86–69, § 3(a)(2)
   ,
   73 Stat. 139
   ;
   Sept. 14, 1960
   ,
   Pub. L. 86–779, § 10(f)
   ,
   74 Stat. 1009
   ;
   Feb. 26, 1964
   ,
   Pub. L. 88–272, title II, § 201(c)
   , (d)(6)(C),
   78 Stat. 32
   ;
   Nov. 13, 1966
   ,
   Pub. L. 89–809, title I, § 103(g)
   ,
   80 Stat. 1552
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title X
   , §§ 1051(h)(2), 1053(d)(1), title XIX, § 1901(a)(20),
   90 Stat. 1647
   , 1649, 1766;
   Apr. 2, 1980
   ,
   Pub. L. 96–223, title IV, § 404(a)
   ,
   94 Stat. 305
   ;
   Aug. 13, 1981
   ,
   Pub. L. 97–34, title III, § 302(b)(2)
   ,
   95 Stat. 272
   ;
   July 18, 1984
   ,
   Pub. L. 98–369, div. A, title V, § 542(b)
   ,
   98 Stat. 891
   , authorized partial exclusion of dividends received by individuals.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to taxable years beginning after
   Dec. 31, 1986
   , see
   section 612(c) of Pub. L. 99–514
   , set out as an Effective Date of 1986 Amendment note under
   section 301 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/