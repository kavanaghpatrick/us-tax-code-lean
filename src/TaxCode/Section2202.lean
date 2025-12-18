/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 115277b9-4d1e-4c02-bc21-49f2125203ab
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
# IRC Section 2202 - Repealed. Pub. L. 94–455, title XIX, § 1902(a)(8), Oct. 4, 1976, 90 Stat. 1805]

This file formalizes IRC §2202 (Repealed. Pub. L. 94–455, title XIX, § 1902(a)(8), Oct. 4, 1976, 90 Stat. 1805]).

## References
- [26 USC §2202](https://www.law.cornell.edu/uscode/text/26/2202)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2202 - Repealed. Pub. L. 94–455, title XIX, § 1902(a)(8), Oct. 4, 1976, 90 Stat. 1805]
   U.S. Code
   Notes
   prev
   |
   next
   Section, acts Aug. 16, 1954, ch. 736,
   68A Stat. 401
   ;
   June 25, 1959
   ,
   Pub. L. 86–70, § 22(a)
   ,
   73 Stat. 146
   ;
   July 12, 1960
   ,
   Pub. L. 86–624, § 18(b)
   ,
   74 Stat. 416
   , related to the presumption that missionaries duly commissioned and serving under boards of foreign missions are residents of the State or the District of Columbia wherein they resided at the time of their commission and departure for service.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to estates of decedents dying after
   Oct. 4, 1976
   , see
   section 1902(c)(1) of Pub. L. 94–455
   , set out as an Effective Date of 1976 Amendment note under
   section 2012 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/