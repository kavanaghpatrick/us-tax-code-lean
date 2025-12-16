/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2bfe8955-1778-486c-8d10-f95e486f9a24
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
# IRC Section 3308 - Instrumentalities of the United States

This file formalizes IRC §3308 (Instrumentalities of the United States).

## References
- [26 USC §3308](https://www.law.cornell.edu/uscode/text/26/3308)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 3308 - Instrumentalities of the United States
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   Notwithstanding any other provision of law (whether enacted before or after the enactment of this section) which grants to any instrumentality of the
   United States
   an exemption from taxation, such instrumentality shall not be exempt from the tax imposed by
   section 3301
   unless such other provision of law grants a specific exemption, by reference to section 3301 (or the corresponding section of prior law), from the tax imposed by such section.
   (Added
   Pub. L. 86–778, title V, § 531(d)(1)
   ,
   Sept. 13, 1960
   ,
   74 Stat. 983
   .)
   Editorial Notes
   References in Text
   Enacted before or after the enactment of this section, referred to in text, means enacted before or after
   Sept. 13, 1960
   , the date of approval of
   Pub. L. 86–778
   .
   Prior Provisions
   A prior
   section 3309
   was renumbered
   section 3311 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date
   Section applicable with respect to remuneration paid after 1961 for services performed after 1961, see
   section 535 of Pub. L. 86–778
   , set out as an Effective Date of 1960 Amendment note under
   section 3305 of this title
   .
   Applicability to Federal Land Banks, Federal Intermediate Credit Banks, and Banks for Cooperatives
   Applicability of this section to Federal land banks, Federal intermediate credit banks, and banks for cooperatives, see
   section 531(g) of Pub. L. 86–778
   , set out as a note under
   section 3305 of this title
   .
   CFR Title
   Parts
   20
   601
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/