/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e31566d6-4a21-4d41-b9d7-3b0bd77b05a0
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a90bad5d-f01e-4a61-94c5-64ff82cd9603
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

structure TaxYear where year : Nat

; h_valid : year ≥ 1913; deriving

DecidableEq, Repr
inductive FilingStatus | Single | MarriedFilingJointly | MarriedFilingSeparately | HeadOfHousehold | QualifyingWidower | Estate | Trust deriving Repr, DecidableEq, Inhabited

/-!
# IRC Section 114 - Repealed. Pub. L. 108–357, title I, § 101(a), Oct. 22, 2004, 118 Stat. 1423]

This file formalizes IRC §114 (Repealed. Pub. L. 108–357, title I, § 101(a), Oct. 22, 2004, 118 Stat. 1423]).

## References
- [26 USC §114](https://www.law.cornell.edu/uscode/text/26/114)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 114 - Repealed. Pub. L. 108–357, title I, § 101(a), Oct. 22, 2004, 118 Stat. 1423]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 106–519, § 3(a)
   ,
   Nov. 15, 2000
   ,
   114 Stat. 2423
   , related to exclusion of extraterritorial income from gross income.
   A prior section 114, act Aug. 16, 1954, ch. 736,
   68A Stat. 35
   , related to sports programs conducted for American National Red Cross, prior to repeal by
   Pub. L. 101–508, title XI, § 11801(a)(8)
   ,
   Nov. 5, 1990
   ,
   104 Stat. 1388–520
   .
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to transactions after
   Dec. 31, 2004
   , see
   section 101(c) of Pub. L. 108–357
   , set out as an Effective Date of 2004 Amendments note under
   section 56 of this title
   .
   Transition Provisions
   Pub. L. 108–357, title I, § 101(d)
   –(f),
   Oct. 22, 2004
   ,
   118 Stat. 1423
   , 1424, as amended by
   Pub. L. 109–222, title V, § 513(b)
   ,
   May 17, 2006
   ,
   120 Stat. 366
   ;
   Pub. L. 113–295, div. A, title II, § 219(a)
   ,
   Dec. 19, 2014
   ,
   128 Stat. 4035
   , provided that:
   “(d)
   Transitional Rule for 2005 and 2006.—
   “(1)
   In general.—
   In the case of transactions during 2005 or 2006, the amount includible in gross income by reason of the amendments made by this section [amending sections
   56
   ,
   275
   ,
   864
   ,
   903
   , and
   999
   of this title and repealing this section and sections
   941
   to
   943
   of this title] shall not exceed the applicable percentage of the amount which would have been so included but for this subsection.
   “(2)
   Applicable percentage.—
   For purposes of paragraph (1), the applicable percentage shall be as follows:
   “(A)
   For 2005, the applicable percentage shall be 20 percent.
   “(B)
   For 2006, the applicable percentage shall be 40 percent.
   “(3)
   Coordination with section 199.—
   This subsection shall be applied without regard to any deduction allowable under section 199 [probably means former section 199 of the
   Internal Revenue Code of 1986
   ].
   “(e)
   Revocation of Election To Be Treated as Domestic Corporation.—
   If, during the 1-year period beginning on the date of the enactment of this Act [
   Oct. 22, 2004
   ], a corporation for which an election is in effect under section 943(e) of the
   Internal Revenue Code of 1986
   revokes such election, no gain or loss shall be recognized with respect to property treated as transferred under clause (ii) of section 943(e)(4)(B) of such Code to the extent such property—
   “(1)
   was treated as transferred under clause (i) thereof, or
   “(2)
   was acquired during a taxable year to which such election applies and before
   May 1, 2003
   , in the ordinary course of its trade or business.
   The Secretary of the Treasury (or such Secretary’s delegate) may prescribe such regulations as may be necessary to prevent the abuse of the purposes of this subsection.
   “[(f)
   Repealed.
   Pub. L. 109–222, title V, § 513(b)
   ,
   May 17, 2006
   ,
   120 Stat. 366
   .]”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/