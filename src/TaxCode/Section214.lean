/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 00ae8560-ecb9-4d42-bef4-c8a80149bc31
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
# IRC Section 214 - Repealed. Pub. L. 94–455, title V, § 504(b)(1), Oct. 4, 1976, 90 Stat. 1565]

This file formalizes IRC §214 (Repealed. Pub. L. 94–455, title V, § 504(b)(1), Oct. 4, 1976, 90 Stat. 1565]).

## References
- [26 USC §214](https://www.law.cornell.edu/uscode/text/26/214)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 214 - Repealed. Pub. L. 94–455, title V, § 504(b)(1), Oct. 4, 1976, 90 Stat. 1565]
   U.S. Code
   Notes
   prev
   |
   next
   Section, acts Aug. 16, 1954, ch. 736,
   68A Stat. 70
   ;
   Apr. 2, 1963
   ,
   Pub. L. 88–4, § 1
   ,
   77 Stat. 4
   ;
   Feb. 26, 1964
   ,
   Pub. L. 88–272, title II, § 212(a)
   ,
   78 Stat. 49
   ;
   Dec. 10, 1971
   ,
   Pub. L. 92–178, title II, § 210(a)
   ,
   85 Stat. 518
   ;
   Mar. 29, 1975
   ,
   Pub. L. 94–12, title II, § 206
   ,
   89 Stat. 32
   , provided for allowance of deduction for household and dependent care services necessary for gainful employment; defined “qualifying individual”, “employment-related expenses”, “maintaining a household”; limitation on deductible amount; income limitation; and special rules and regulations applicable in the determination and allowance of deduction.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to taxable years beginning after
   Dec. 31, 1975
   , see
   section 508 of Pub. L. 94–455
   , set out as an Effective Date of 1976 Amendment note under
   section 3 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/