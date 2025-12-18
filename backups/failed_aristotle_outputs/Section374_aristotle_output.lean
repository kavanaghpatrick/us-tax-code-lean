/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 04bf8b9f-b9d5-4797-b7da-7be05da4fe4f
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
# IRC Section 374 - Repealed. Pub. L. 101–508, title XI, § 11801(a)(19), Nov. 5, 1990, 104 Stat. 1388–521]

This file formalizes IRC §374 (Repealed. Pub. L. 101–508, title XI, § 11801(a)(19), Nov. 5, 1990, 104 Stat. 1388–521]).

## References
- [26 USC §374](https://www.law.cornell.edu/uscode/text/26/374)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 374 - Repealed. Pub. L. 101–508, title XI, § 11801(a)(19), Nov. 5, 1990, 104 Stat. 1388–521]
   U.S. Code
   Notes
   prev
   | next
   Section, added June 29, 1956, ch. 463, § 1,
   70 Stat. 402
   ; amended
   Mar. 31, 1976
   ,
   Pub. L. 94–253, § 1(a)
   , (d),
   90 Stat. 295
   , 296;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIX, § 1901(a)(53)
   , (b)(10)(A), (14)(B), (C),
   90 Stat. 1773
   , 1795, 1796;
   Nov. 6, 1978
   ,
   Pub. L. 95–600, title III, § 369(a)
   ,
   92 Stat. 2857
   ;
   Apr. 1, 1980
   ,
   Pub. L. 96–222, title I, § 103(a)(14)
   ,
   94 Stat. 214
   ;
   Oct. 22, 1986
   ,
   Pub. L. 99–514, title XVIII, § 1899A(9)
   ,
   100 Stat. 2958
   , related to nonrecognition of gain or loss in certain railroad reorganizations.
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