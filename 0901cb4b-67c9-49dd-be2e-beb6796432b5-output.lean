/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0901cb4b-67c9-49dd-be2e-beb6796432b5
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
# IRC Section 878 - Foreign educational, charitable, and certain other exempt organizations

This file formalizes IRC §878 (Foreign educational, charitable, and certain other exempt organizations).

## References
- [26 USC §878](https://www.law.cornell.edu/uscode/text/26/878)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 878 - Foreign educational, charitable, and certain other exempt organizations
   U.S. Code
   Notes
   prev
   |
   next
   For special provisions relating to foreign educational, charitable, and other exempt organizations, see sections 512(a) and 4948.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 282
   , § 877; renumbered § 878,
   Pub. L. 89–809, title I, § 103(f)(1)
   ,
   Nov. 13, 1966
   ,
   80 Stat. 1551
   ; amended
   Pub. L. 91–172, title I, § 101(j)(20)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 528
   .)
   Editorial Notes
   Amendments
   1969—
   Pub. L. 91–172
   substituted provisions requiring reference to organizations in sections 512(a) and 4948 for provisions requiring reference to trusts in section 512(a), and struck out reference to unrelated business income.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1969 Amendment
   Amendment by
   Pub. L. 91–172
   applicable to taxable years beginning after
   Dec. 31, 1969
   , see
   section 101(k)(2)(B) of Pub. L. 91–172
   , set out as an Effective Date note under
   section 4940 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/