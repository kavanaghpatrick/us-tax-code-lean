/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 603d89a3-bf1b-444f-a84c-5d0c5fb6dd38
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
# IRC Section 333 - Repealed. Pub. L. 99–514, title VI, § 631(e)(3), Oct. 22, 1986, 100 Stat. 2273]

This file formalizes IRC §333 (Repealed. Pub. L. 99–514, title VI, § 631(e)(3), Oct. 22, 1986, 100 Stat. 2273]).

## References
- [26 USC §333](https://www.law.cornell.edu/uscode/text/26/333)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 333 - Repealed. Pub. L. 99–514, title VI, § 631(e)(3), Oct. 22, 1986, 100 Stat. 2273]
   U.S. Code
   Notes
   prev
   |
   next
   Section, acts Aug. 16, 1954, ch. 736,
   68A Stat. 103
   ;
   Feb. 26, 1964
   ,
   Pub. L. 88–272, title II, § 225(g)
   ,
   78 Stat. 89
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIX
   , §§ 1901(a)(44), 1906(b)(13)(A), 1951(b)(6)(A),
   90 Stat. 1772
   , 1834, 1838, related to election as to recognition of gain in certain liquidations.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal applicable to any distribution in complete liquidation, and any sale or exchange, made by a corporation after
   July 31, 1986
   , unless such corporation is completely liquidated before
   Jan. 1, 1987
   , any transaction described in
   section 338 of this title
   for which the acquisition date occurs after
   Dec. 31, 1986
   , and any distribution, not in complete liquidation, made after
   Dec. 31, 1986
   , with exceptions and special and transitional rules, see
   section 633 of Pub. L. 99–514
   , set out as an Effective Date note under
   section 336 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/