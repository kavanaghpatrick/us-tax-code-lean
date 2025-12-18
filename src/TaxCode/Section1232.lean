/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5ba87ee0-9b82-4dcc-8e4a-1da1dbec4edd
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
# IRC Section 1232 - 26 U.S. Code § 1232 to 1232B - Repealed. Pub. L. 98–369, div. A, title I, § 42(a)(1), July 18, 1984, 98 Stat. 556]

This file formalizes IRC §1232 (26 U.S. Code § 1232 to 1232B - Repealed. Pub. L. 98–369, div. A, title I, § 42(a)(1), July 18, 1984, 98 Stat. 556]).

## References
- [26 USC §1232](https://www.law.cornell.edu/uscode/text/26/1232)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1232 to 1232B - Repealed. Pub. L. 98–369, div. A, title I, § 42(a)(1), July 18, 1984, 98 Stat. 556]
   U.S. Code
   Notes
   prev
   |
   next
   Section 1232, acts Aug. 16, 1954, ch. 736,
   68A Stat. 326
   ;
   Sept. 2, 1958
   ,
   Pub. L. 85–866, title I
   , §§ 50(a), 51,
   72 Stat. 1642
   , 1643;
   June 25, 1959
   ,
   Pub. L. 86–69, § 3(e)
   ,
   73 Stat. 140
   ;
   Sept. 2, 1964
   ,
   Pub. L. 88–563, § 5
   ,
   78 Stat. 845
   ;
   Dec. 30, 1969
   ,
   Pub. L. 91–172, title IV, § 413(a)
   , (b),
   83 Stat. 609
   , 611;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIV, § 1402(b)(1)(S)
   , (2), title XIX, §§ 1901(b)(3)(I), (14)(D), 1904(b)(10)(C),
   90 Stat. 1732
   , 1793, 1796, 1817;
   Aug. 13, 1981
   ,
   Pub. L. 97–34, title V, § 505(b)
   ,
   95 Stat. 331
   ;
   Sept. 3, 1982
   ,
   Pub. L. 97–248, title II
   , §§ 231(c), 232(b), title III, § 310(b)(6),
   96 Stat. 499
   , 501, 599;
   Jan. 12, 1983
   ,
   Pub. L. 97–448, title III, § 306(a)(9)(B)
   , (C)(i), (ii),
   96 Stat. 2403
   , 2404;
   July 18, 1984
   ,
   Pub. L. 98–369, div. A, title X, § 1001(b)(16)
   , (d), (e),
   98 Stat. 1012
   , related to bonds and other evidences of indebtedness. See section 1271 et seq. of this title.
   Section 1232A, added
   Pub. L. 97–248, title II, § 231(a)
   ,
   Sept. 3, 1982
   ,
   96 Stat. 496
   ; amended
   Pub. L. 98–369, div. A, title II, § 211(b)(17)
   ,
   July 18, 1984
   ,
   98 Stat. 756
   , related to original issue discount. See section 1271 et seq. of this title.
   Section 1232B, added
   Pub. L. 97–248, title II, § 232(a)
   ,
   Sept. 3, 1982
   ,
   96 Stat. 499
   , related to stripped bonds. See
   section 1286 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to taxable years ending after
   July 18, 1984
   , see
   section 44 of Pub. L. 98–369
   , set out as an Effective Date note under
   section 1271 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/