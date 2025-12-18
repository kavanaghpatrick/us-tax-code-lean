/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 69853455-b872-4e8e-9f23-ab73e23af9f9
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
# IRC Section 386 - Repealed. Pub. L. 100–647, title I, § 1006(e)(8)(A), Nov. 10, 1988, 102 Stat. 3401]

This file formalizes IRC §386 (Repealed. Pub. L. 100–647, title I, § 1006(e)(8)(A), Nov. 10, 1988, 102 Stat. 3401]).

## References
- [26 USC §386](https://www.law.cornell.edu/uscode/text/26/386)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 386 - Repealed. Pub. L. 100–647, title I, § 1006(e)(8)(A), Nov. 10, 1988, 102 Stat. 3401]
   U.S. Code
   Notes
   prev |
   next
   Section, added
   Pub. L. 98–369, div. A, title I, § 75(a)
   ,
   July 18, 1984
   ,
   98 Stat. 594
   ; amended
   Pub. L. 99–514, title XVIII, § 1805(c)(1)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2810
   , related to transfers of partnership and trust interests by corporations.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal effective, except as otherwise provided, as if included in the provision of the
   Tax Reform Act of 1986
   ,
   Pub. L. 99–514
   , to which such amendment relates, see
   section 1019(a) of Pub. L. 100–647
   , set out as an Effective Date of 1988 Amendment note under
   section 1 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/