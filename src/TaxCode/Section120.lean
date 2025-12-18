/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e4da07c8-390f-4c6d-82dd-65400fec6da7
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d139a6ed-7006-4ae2-a9e9-39502bd0cd0d
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
# IRC Section 120 - Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(19)(A), Dec. 19, 2014, 128 Stat. 4039]

This file formalizes IRC §120 (Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(19)(A), Dec. 19, 2014, 128 Stat. 4039]).

## References
- [26 USC §120](https://www.law.cornell.edu/uscode/text/26/120)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 120 - Repealed. Pub. L. 113–295, div. A, title II, § 221(a)(19)(A), Dec. 19, 2014, 128 Stat. 4039]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 94–455, title XXI, § 2134(a)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1926
   ; amended
   Pub. L. 97–34, title VIII, § 802(a)
   ,
   Aug. 13, 1981
   ,
   95 Stat. 349
   ;
   Pub. L. 97–448, title I, § 108(a)
   ,
   Jan. 12, 1983
   ,
   96 Stat. 2391
   ;
   Pub. L. 98–612, § 1(a)
   , (b)(3)(A),
   Oct. 31, 1984
   ,
   98 Stat. 3180
   , 3181;
   Pub. L. 99–514, title XI
   , §§ 1114(b)(3), 1151(c)(3), (g)(1), 1162(b),
   Oct. 22, 1986
   ,
   100 Stat. 2450
   , 2503, 2506, 2510;
   Pub. L. 100–647, title I, § 1011B(a)(31)(B)
   , title IV, § 4002(a), (b)(1),
   Nov. 10, 1988
   ,
   102 Stat. 3488
   , 3643;
   Pub. L. 101–140, title II, § 203(a)(1)
   , (2),
   Nov. 8, 1989
   ,
   103 Stat. 830
   ;
   Pub. L. 101–239, title VII, § 7102(a)(1)
   ,
   Dec. 19, 1989
   ,
   103 Stat. 2305
   ;
   Pub. L. 101–508, title XI, § 11404(a)
   ,
   Nov. 5, 1990
   ,
   104 Stat. 1388–473
   ;
   Pub. L. 102–227, title I, § 104(a)(1)
   ,
   Dec. 11, 1991
   ,
   105 Stat. 1687
   ;
   Pub. L. 108–311, title II, § 207(10)
   ,
   Oct. 4, 2004
   ,
   118 Stat. 1177
   , related to amounts received under qualified group legal services plans.
   A prior section 120, act Aug. 16, 1954, ch. 736,
   68A Stat. 39
   , related to statutory subsistence allowance received by police, prior to repeal by
   Pub. L. 85–866, title I, § 3(a)
   , (c),
   Sept. 2, 1958
   ,
   72 Stat. 1607
   , effective with respect to taxable years ending after
   Sept. 30, 1958
   , but only with respect to amounts received as a statutory subsistence allowance for any day after
   Sept. 30, 1958
   .
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