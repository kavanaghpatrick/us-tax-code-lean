/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 85e20000-3ed0-44c4-8c2a-969418ffe613
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
# IRC Section 847 - Repealed. Pub. L. 115–97, title I, § 13516(a), Dec. 22, 2017, 131 Stat. 2144]

This file formalizes IRC §847 (Repealed. Pub. L. 115–97, title I, § 13516(a), Dec. 22, 2017, 131 Stat. 2144]).

## References
- [26 USC §847](https://www.law.cornell.edu/uscode/text/26/847)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 847 - Repealed. Pub. L. 115–97, title I, § 13516(a), Dec. 22, 2017, 131 Stat. 2144]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 100–647, title VI, § 6077(a)
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3707
   ; amended
   Pub. L. 101–239, title VII, § 7816(n)
   ,
   Dec. 19, 1989
   ,
   103 Stat. 2422
   ;
   Pub. L. 115–97, title I, § 12001(b)(8)(B)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2093
   , related to special estimated tax payments.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Pub. L. 115–97, title I, § 13516(b)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2144
   , provided that:
   “The amendments made by this section [repealing this section] shall apply to taxable years beginning after
   December 31, 2017
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/