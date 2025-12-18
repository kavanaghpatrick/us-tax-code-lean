/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 21892714-cea0-4003-a419-3ba55a8f556e
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
# IRC Section 370 - 26 U.S. Code § 370 to 372 - Repealed. Pub. L. 101–508, title XI, § 11801(a)(19), Nov. 5, 1990, 104 Stat. 1388–521]

This file formalizes IRC §370 (26 U.S. Code § 370 to 372 - Repealed. Pub. L. 101–508, title XI, § 11801(a)(19), Nov. 5, 1990, 104 Stat. 1388–521]).

## References
- [26 USC §370](https://www.law.cornell.edu/uscode/text/26/370)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 370 to 372 - Repealed. Pub. L. 101–508, title XI, § 11801(a)(19), Nov. 5, 1990, 104 Stat. 1388–521]
   U.S. Code
   Notes
   prev |
   next
   Section 370, added
   Pub. L. 96–589, § 4(f)
   ,
   Dec. 24, 1980
   ,
   94 Stat. 3404
   , related to termination of part.
   Section 371, acts Aug. 16, 1954, ch. 736,
   68A Stat. 121
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIX, § 1901(a)(50)
   ,
   90 Stat. 1773
   , related to reorganization in certain receivership and bankruptcy proceedings.
   Section 372, acts Aug. 16, 1954, ch. 736,
   68A Stat. 122
   ;
   Sept. 2, 1958
   ,
   Pub. L. 85–866, title I, § 95(a)
   ,
   72 Stat. 1671
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIX
   , §§ 1901(a)(51), (b)(14)(A), 1906(b)(13)(A),
   90 Stat. 1773
   , 1795, 1834, related to basis in connection with certain receivership and bankruptcy proceedings.
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