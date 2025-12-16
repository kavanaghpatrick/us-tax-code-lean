/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9a2d8cf6-ac99-4e24-bade-6e8fd9007b09
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
# IRC Section 1036 - Stock for stock of same corporation

This file formalizes IRC §1036 (Stock for stock of same corporation).

## References
- [26 USC §1036](https://www.law.cornell.edu/uscode/text/26/1036)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1036 - Stock for stock of same corporation
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   No gain or loss shall be recognized if common stock in a corporation is exchanged solely for common stock in the same corporation, or if preferred stock in a corporation is exchanged solely for preferred stock in the same corporation.
   (b)
   Nonqualified preferred stock not treated as stock
   For purposes of this section, nonqualified preferred stock (as defined in
   section 351(g)(2)
   ) shall be treated as property other than stock.
   (c)
   Cross references
   (1)
   For rules relating to recognition of gain or loss where an exchange is not solely in kind, see subsections (b) and (c) of section 1031.
   (2)
   For rules relating to the basis of property acquired in an exchange described in subsection (a), see subsection (d) of section 1031.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 309
   ;
   Pub. L. 105–34, title X, § 1014(e)(3)
   ,
   Aug. 5, 1997
   ,
   111 Stat. 921
   .)
   Editorial Notes
   Amendments
   1997—Subsecs. (b), (c).
   Pub. L. 105–34
   added subsec. (b) and redesignated former subsec. (b) as (c).
   Statutory Notes and Related Subsidiaries
   Effective Date of 1997 Amendment
   Amendment by
   Pub. L. 105–34
   applicable, with certain exceptions, to transactions after
   June 8, 1997
   , see
   section 1014(f) of Pub. L. 105–34
   , set out as a note under
   section 351 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/