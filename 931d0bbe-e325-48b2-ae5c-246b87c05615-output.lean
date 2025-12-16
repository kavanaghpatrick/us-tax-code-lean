/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 931d0bbe-e325-48b2-ae5c-246b87c05615
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
# IRC Section 2208 - Certain residents of possessions considered citizens of the United States

This file formalizes IRC §2208 (Certain residents of possessions considered citizens of the United States).

## References
- [26 USC §2208](https://www.law.cornell.edu/uscode/text/26/2208)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2208 - Certain residents of possessions considered citizens of the United States
   U.S. Code
   Notes
   prev
   |
   next
   A decedent who was a citizen of the United States and a resident of a possession thereof at the time of his death shall, for purposes of the tax imposed by this chapter, be considered a “citizen” of the United States within the meaning of that term wherever used in this title unless he acquired his United States citizenship solely by reason of (1) his being a citizen of such possession of the United States, or (2) his birth or residence within such possession of the United States.
   (Added
   Pub. L. 85–866, title I, § 102(a)
   ,
   Sept. 2, 1958
   ,
   72 Stat. 1674
   .)
   Statutory Notes and Related Subsidiaries
   Effective Date
   Section applicable to estates of decedents dying after
   Sept. 2, 1958
   , see
   section 102(d) of Pub. L. 85–866
   , set out as an Effective Date of 1958 Amendment note under
   section 2014 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/