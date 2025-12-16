/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a616a1d1-6445-4a18-bd57-49743b3054b7
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
# IRC Section 1101 - 26 U.S. Code § 1101 to 1103 - Repealed. Pub. L. 101–508, title XI, § 11801(a)(34), Nov. 5, 1990, 104 Stat. 1388–521]

This file formalizes IRC §1101 (26 U.S. Code § 1101 to 1103 - Repealed. Pub. L. 101–508, title XI, § 11801(a)(34), Nov. 5, 1990, 104 Stat. 1388–521]).

## References
- [26 USC §1101](https://www.law.cornell.edu/uscode/text/26/1101)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1101 to 1103 - Repealed. Pub. L. 101–508, title XI, § 11801(a)(34), Nov. 5, 1990, 104 Stat. 1388–521]
   U.S. Code
   Notes
   Section 1101, added May 9, 1956, ch. 240, § 10(a),
   70 Stat. 139
   ; amended
   Oct. 2, 1976
   ,
   Pub. L. 94–452, § 2(a)
   ,
   90 Stat. 1503
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   90 Stat. 1834
   ;
   Oct. 19, 1982
   ,
   Pub. L. 97–354, § 5(a)(34)
   ,
   96 Stat. 1695
   , related to distributions of property pursuant to Bank Holding Company Act.
   Section 1102, added May 9, 1956, ch. 240, § 10(a),
   70 Stat. 143
   ; amended
   Dec. 27, 1967
   ,
   Pub. L. 90–225, § 1
   ,
   81 Stat. 730
   ;
   Oct. 2, 1976
   ,
   Pub. L. 94–452, § 2(a)
   ,
   90 Stat. 1508
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   90 Stat. 1834
   , related to basis of property acquired in distributions, periods of limitation, allocation of earnings and profits, and itemization of property.
   Section 1103, added May 9, 1956, ch. 240, § 10(a),
   70 Stat. 144
   ; amended
   Oct. 2, 1976
   ,
   Pub. L. 94–452, § 2(a)
   ,
   90 Stat. 1509
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   90 Stat. 1834
   , related to definitions for this part.
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