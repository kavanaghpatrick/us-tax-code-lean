/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b13f4825-3e79-4cde-954e-7f4803d60b3f
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
# IRC Section 1564 - Repealed. Pub. L. 101–508, title XI, § 11801(a)(38), Nov. 5, 1990, 104 Stat. 1388–521]

This file formalizes IRC §1564 (Repealed. Pub. L. 101–508, title XI, § 11801(a)(38), Nov. 5, 1990, 104 Stat. 1388–521]).

## References
- [26 USC §1564](https://www.law.cornell.edu/uscode/text/26/1564)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1564 - Repealed. Pub. L. 101–508, title XI, § 11801(a)(38), Nov. 5, 1990, 104 Stat. 1388–521]
   U.S. Code
   Notes
   prev
   | next
   Section, added
   Pub. L. 91–172, title IV, § 401(b)(1)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 600
   ; amended
   Pub. L. 94–455, title XIX
   , §§ 1901(b)(1)(J)(vi), (21)(A)(ii), 1906(b)(13)(A),
   Oct. 4, 1976
   ,
   90 Stat. 1791
   , 1797, 1834, related to transitional rules in the case of certain controlled corporations.
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