/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dbe77527-499e-4701-b5f7-98c1d805b390
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
# IRC Section 107 - Rental value of parsonages

This file formalizes IRC §107 (Rental value of parsonages).

## References
- [26 USC §107](https://www.law.cornell.edu/uscode/text/26/107)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 107 - Rental value of parsonages
   U.S. Code
   Notes
   prev
   |
   next
   In the case of a minister of the gospel, gross income does not include—
   (1)
   the rental value of a home furnished to him as part of his
   compensation
   ; or
   (2)
   the rental allowance paid to him as part of his
   compensation
   , to the extent used by him to rent or provide a home and to the extent such allowance does not exceed the fair rental value of the home, including furnishings and appurtenances such as a garage, plus the cost of utilities.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 32
   ;
   Pub. L. 107–181, § 2(a)
   ,
   May 20, 2002
   ,
   116 Stat. 583
   .)
   Editorial Notes
   Amendments
   2002—Par. (2).
   Pub. L. 107–181
   inserted “and to the extent such allowance does not exceed the fair rental value of the home, including furnishings and appurtenances such as a garage, plus the cost of utilities” before period at end.
   Statutory Notes and Related Subsidiaries
   Effective Date of 2002 Amendment
   Pub. L. 107–181, § 2(b)
   ,
   May 20, 2002
   ,
   116 Stat. 583
   , provided that:
   “(1)
   In general.—
   The amendment made by this section [amending this section] shall apply to taxable years beginning after
   December 31, 2001
   .
   “(2)
   Returns positions.—
   The amendment made by this section also shall apply to any taxable year beginning before
   January 1, 2002
   , for which the taxpayer—
   “(A)
   on a return filed before
   April 17, 2002
   , limited the exclusion under section 107 of the
   Internal Revenue Code of 1986
   as provided in such amendment, or
   “(B)
   filed a return after
   April 16, 2002
   .
   “(3)
   Other years before 2002.—
   Except as provided in paragraph (2), notwithstanding any prior regulation, revenue ruling, or other guidance issued by the
   Internal Revenue Service
   , no person shall be subject to the limitations added to section 107 of such Code by this Act for any taxable year beginning before
   January 1, 2002
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/