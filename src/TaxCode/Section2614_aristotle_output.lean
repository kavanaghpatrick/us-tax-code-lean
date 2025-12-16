/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7be43aca-c6a3-427d-965b-241b26edec80
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
# IRC Section 2614 - Omitted]

This file formalizes IRC §2614 (Omitted]).

## References
- [26 USC §2614](https://www.law.cornell.edu/uscode/text/26/2614)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2614 - Omitted]
   U.S. Code
   Notes
   prev
   | next
   Editorial Notes
   Codification
   Section, added
   Pub. L. 94–455, title XX, § 2006(a)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1887
   ; amended
   Pub. L. 95–600, title VII, § 702(c)(1)(B)
   ,
   Nov. 6, 1978
   ,
   92 Stat. 2926
   ;
   Pub. L. 96–223, title IV, § 401(c)(3)
   ,
   Apr. 2, 1980
   ,
   94 Stat. 300
   , related to special rules for
   generation-skipping transfers,
   prior to the general revision of this chapter by
   Pub. L. 99–514, § 1431(a)
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/