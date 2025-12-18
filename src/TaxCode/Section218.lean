/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6dc15181-2688-4eab-99bb-f166c0399a25
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
# IRC Section 218 - Repealed. Pub. L. 95–600, title I, § 113(a)(1), Nov. 6, 1978, 92 Stat. 2778]

This file formalizes IRC §218 (Repealed. Pub. L. 95–600, title I, § 113(a)(1), Nov. 6, 1978, 92 Stat. 2778]).

## References
- [26 USC §218](https://www.law.cornell.edu/uscode/text/26/218)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 218 - Repealed. Pub. L. 95–600, title I, § 113(a)(1), Nov. 6, 1978, 92 Stat. 2778]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 92–178, title VII, § 702(a)
   ,
   Dec. 10, 1971
   ,
   85 Stat. 561
   ; amended
   Pub. L. 93–625
   , §§ 11(d), 12(b),
   Jan. 3, 1975
   ,
   88 Stat. 2120
   ;
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1834
   , related to contributions to candidates for public office.
   A prior
   section 218
   was renumbered
   section 226 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal effective with respect to contributions the payment of which is made after
   Dec. 31, 1978
   , in taxable years beginning after such date, see
   section 113(d) of Pub. L. 95–600
   , set out as an Effective Date of 1978 Amendment note under
   section 24 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/