/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2d6d7f90-d391-445d-ac4d-4955b7e4e06f
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
# IRC Section 1022 - Repealed. Pub. L. 111–312, title III, § 301(a), Dec. 17, 2010, 124 Stat. 3300]

This file formalizes IRC §1022 (Repealed. Pub. L. 111–312, title III, § 301(a), Dec. 17, 2010, 124 Stat. 3300]).

## References
- [26 USC §1022](https://www.law.cornell.edu/uscode/text/26/1022)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1022 - Repealed. Pub. L. 111–312, title III, § 301(a), Dec. 17, 2010, 124 Stat. 3300]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added
   Pub. L. 107–16, title V, § 542(a)
   ,
   June 7, 2001
   ,
   115 Stat. 76
   , related to treatment of property acquired from a decedent dying after
   Dec. 31, 2009
   .
   A prior section 1022, added
   Pub. L. 88–272, title II, § 225(j)(1)
   ,
   Feb. 26, 1964
   ,
   78 Stat. 92
   , dealt with the increase in basis with respect to certain foreign personal holding company stock or securities, prior to repeal by
   Pub. L. 94–455, title XIX, § 1901(a)(126)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1784
   , applicable with respect to stock or securities acquired from a decedent dying after
   Oct. 4, 1976
   .
   Another prior section 1022, act Aug. 16, 1954, ch. 736,
   68A Stat. 302
   , relating to cross references, was renumbered section 1023.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Repeal of section applicable to estates of decedents dying, and transfers made after
   Dec. 31, 2009
   , except as otherwise provided, see
   section 301(e) of Pub. L. 111–312
   , set out as an Effective and Termination Dates of 2010 Amendment note under
   section 121 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/