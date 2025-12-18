/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c30e5b80-b558-450e-8d42-526485068595
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
# IRC Section 280 - Repealed. Pub. L. 99–514, title VIII, § 803(b)(2)(A), Oct. 22, 1986, 100 Stat. 2355]

This file formalizes IRC §280 (Repealed. Pub. L. 99–514, title VIII, § 803(b)(2)(A), Oct. 22, 1986, 100 Stat. 2355]).

## References
- [26 USC §280](https://www.law.cornell.edu/uscode/text/26/280)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 280 - Repealed. Pub. L. 99–514, title VIII, § 803(b)(2)(A), Oct. 22, 1986, 100 Stat. 2355]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 94–455, title II, § 210(a)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1544
   ; amended
   Pub. L. 95–600, title VII, § 701(m)(2)
   ,
   Nov. 6, 1978
   ,
   92 Stat. 2907
   ;
   Pub. L. 97–354, § 5(a)(25)
   ,
   Oct. 19, 1982
   ,
   96 Stat. 1694
   , related to certain
   expenditures
   incurred in the production of films, books, records, or similar property.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   If any
   interest
   costs incurred after
   Dec. 31, 1986
   , are attributable to costs incurred before
   Jan. 1, 1987
   , the repeal of this section is applicable to such
   interest
   costs only to the extent such
   interest
   costs are attributable to costs which were required to be capitalized under section 263 of the
   Internal Revenue Code of 1954
   and which would have been taken into account in applying section 189 of the
   Internal Revenue Code of 1954
   (as in effect before its repeal by
   section 803 of Pub. L. 99–514
   ) or, if applicable, section 266 of such Code, see
   section 7831(d)(2) of Pub. L. 101–239
   , set out as an Effective Date note under
   section 263A of this title
   .
   Repeal applicable to costs incurred after
   Dec. 31, 1986
   , in taxable years ending after such date, except as otherwise provided, see
   section 803(d) of Pub. L. 99–514
   , set out as an Effective Date note under
   section 263A of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/