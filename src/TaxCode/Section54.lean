/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: de29a8f3-bf74-449a-a6a0-16ff3cf5d3df
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2b7ed031-9a3d-42fa-9a74-01d73d0d53ea
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
# IRC Section 54 - Repealed. Pub. L. 115–97, title I, § 13404(a), Dec. 22, 2017, 131 Stat. 2138]

This file formalizes IRC §54 (Repealed. Pub. L. 115–97, title I, § 13404(a), Dec. 22, 2017, 131 Stat. 2138]).

## References
- [26 USC §54](https://www.law.cornell.edu/uscode/text/26/54)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 54 - Repealed. Pub. L. 115–97, title I, § 13404(a), Dec. 22, 2017, 131 Stat. 2138]
   U.S. Code
   Notes
   Section, added
   Pub. L. 109–58, title XIII, § 1303(a)
   ,
   Aug. 8, 2005
   ,
   119 Stat. 992
   ; amended
   Pub. L. 109–135, title I, § 101(b)(1)
   , title IV, § 402(c)(1),
   Dec. 21, 2005
   ,
   119 Stat. 2593
   , 2610;
   Pub. L. 109–222, title V, § 508(d)(3)
   ,
   May 17, 2006
   ,
   120 Stat. 362
   ;
   Pub. L. 109–432, div. A, title I, § 107(b)(2)
   , title II, § 202(a),
   Dec. 20, 2006
   ,
   120 Stat. 2939
   , 2944;
   Pub. L. 110–234, title XV, § 15316(c)(1)
   ,
   May 22, 2008
   ,
   122 Stat. 1511
   ;
   Pub. L. 110–246, § 4(a)
   , title XV, § 15316(c)(1),
   June 18, 2008
   ,
   122 Stat. 1664
   , 2273;
   Pub. L. 110–343, div. B, title I, § 107(c)
   ,
   Oct. 3, 2008
   ,
   122 Stat. 3819
   ;
   Pub. L. 111–5, div. B, title I
   , §§ 1531(c)(3), 1541(b)(1),
   Feb. 17, 2009
   ,
   123 Stat. 360
   , 362;
   Pub. L. 115–97, title I, § 13404(c)(2)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2138
   , related to credit to holders of clean
   renewable energy
   bonds.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Pub. L. 115–97, title I, § 13404(d)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2138
   , provided that:
   “The amendments made by this section [amending this section and sections
   6211
   and
   6401
   of this title and repealing this section and sections
   54A
   to
   54F
   ,
   54AA
   ,
   1397E
   , and
   6431
   of this title] shall apply to bonds issued after
   December 31, 2017
   .”
   Regulations
   Pub. L. 109–58, title XIII, § 1303(d)
   ,
   Aug. 8, 2005
   ,
   119 Stat. 997
   , provided that the Secretary of the Treasury was to issue regulations required under former
   26 U.S.C. 54
   not later than 120 days after
   Aug. 8, 2005
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/