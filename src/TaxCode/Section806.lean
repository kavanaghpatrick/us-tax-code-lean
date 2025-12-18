/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: eb4883bb-87b3-49d7-a608-651121704bce
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
# IRC Section 806 - Repealed. Pub. L. 115–97, title I, § 13512(a), Dec. 22, 2017, 131 Stat. 2142]

This file formalizes IRC §806 (Repealed. Pub. L. 115–97, title I, § 13512(a), Dec. 22, 2017, 131 Stat. 2142]).

## References
- [26 USC §806](https://www.law.cornell.edu/uscode/text/26/806)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 806 - Repealed. Pub. L. 115–97, title I, § 13512(a), Dec. 22, 2017, 131 Stat. 2142]
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
   98 Stat. 724
   ; amended
   Pub. L. 99–514, title X, § 1011(a)
   , (b)(5)–(8), (11)(A),
   Oct. 22, 1986
   ,
   100 Stat. 2388
   , 2389, related to small life insurance company deduction.
   A prior section 806, added
   Pub. L. 86–69, § 2(a)
   ,
   June 25, 1959
   ,
   73 Stat. 120
   ; amended
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1834
   , related to certain changes in reserves and assets, prior to the general revision of this part by
   Pub. L. 98–369, § 211(a)
   .
   Another prior section 806, act Aug. 16, 1954, ch. 736,
   68A Stat. 258
   , related to adjustment for certain reserves, prior to the general revision of this part by act Mar. 13, 1956, ch. 83, § 2,
   70 Stat. 36
   .
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to taxable years beginning after
   Dec. 31, 2017
   , see
   section 13512(c) of Pub. L. 115–97
   , set out as an Effective Date of 2017 Amendment note under
   section 453B of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/