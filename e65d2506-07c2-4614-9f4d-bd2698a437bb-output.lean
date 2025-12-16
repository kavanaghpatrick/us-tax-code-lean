/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e65d2506-07c2-4614-9f4d-bd2698a437bb
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
# IRC Section 586 - Repealed. Pub. L. 99–514, title IX, § 901(c), Oct. 22, 1986, 100 Stat. 2378]

This file formalizes IRC §586 (Repealed. Pub. L. 99–514, title IX, § 901(c), Oct. 22, 1986, 100 Stat. 2378]).

## References
- [26 USC §586](https://www.law.cornell.edu/uscode/text/26/586)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 586 - Repealed. Pub. L. 99–514, title IX, § 901(c), Oct. 22, 1986, 100 Stat. 2378]
   U.S. Code
   Notes
   prev
   | next
   Section, added
   Pub. L. 91–172, title IV, § 431(a)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 618
   ; amended
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1834
   , related to reserves for losses on loans of small business investment companies, etc.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to taxable years beginning after
   Dec. 31, 1986
   , see
   section 901(e) of Pub. L. 99–514
   , set out as an Effective Date of 1986 Amendment note under
   section 166 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/