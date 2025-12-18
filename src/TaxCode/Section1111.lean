/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b70f363f-66ba-4aa9-b83b-476d41ac34a3
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
# IRC Section 1111 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(134), Oct. 4, 1976, 90 Stat. 1786]

This file formalizes IRC §1111 (Repealed. Pub. L. 94–455, title XIX, § 1901(a)(134), Oct. 4, 1976, 90 Stat. 1786]).

## References
- [26 USC §1111](https://www.law.cornell.edu/uscode/text/26/1111)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1111 - Repealed. Pub. L. 94–455, title XIX, § 1901(a)(134), Oct. 4, 1976, 90 Stat. 1786]
   U.S. Code
   Notes
   Section, added
   Pub. L. 87–403, § 1(a)
   ,
   Feb. 2, 1962
   ,
   76 Stat. 4
   , related to distribution of stock pursuant to order enforcing antitrust laws.
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/