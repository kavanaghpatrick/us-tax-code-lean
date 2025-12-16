/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dd014116-2ea3-4f07-b95e-65fe0f849ab6
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
# IRC Section 124 - Repealed. Pub. L. 101–508, title XI, § 11801(a)(9), Nov. 5, 1990, 104 Stat. 1388–520]

This file formalizes IRC §124 (Repealed. Pub. L. 101–508, title XI, § 11801(a)(9), Nov. 5, 1990, 104 Stat. 1388–520]).

## References
- [26 USC §124](https://www.law.cornell.edu/uscode/text/26/124)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 124 - Repealed. Pub. L. 101–508, title XI, § 11801(a)(9), Nov. 5, 1990, 104 Stat. 1388–520]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 95–618, title II, § 242(a)
   ,
   Nov. 9, 1978
   ,
   92 Stat. 3193
   , related to qualified transportation provided by employers.
   A prior
   section 124
   was renumbered
   section 140 of this title
   .
   Statutory Notes and Related Subsidiaries
   Savings Provision
   For provisions that nothing in repeal by
   Pub. L. 101–508
   be construed to affect treatment of certain transactions occurring, property acquired, or items of income, loss, deduction, or credit taken into account prior to
   Nov. 5, 1990
   , for purposes of determining liability for tax for periods ending after
   Nov. 5, 1990
   , see
   section 11821(b) of Pub. L. 101–508
   , set out as a note under
   section 45K of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/