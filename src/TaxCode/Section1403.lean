/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 75e642d4-0164-485f-9b11-b948f34764fe
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
# IRC Section 1403 - Miscellaneous provisions

This file formalizes IRC §1403 (Miscellaneous provisions).

## References
- [26 USC §1403](https://www.law.cornell.edu/uscode/text/26/1403)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1403 - Miscellaneous provisions
   U.S. Code
   Notes
   prev
   | next
   (a)
   Title of chapter
   This chapter may be cited as the “
   Self-Employment Contributions Act of 1954
   ”.
   (b)
   Cross references
   (1)
   For provisions relating to returns, see section 6017.
   (2)
   For provisions relating to collection of taxes in Virgin Islands, Guam, American Samoa, and Puerto
   Rico
   , see section 7651.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 355
   ;
   Pub. L. 86–778, title I, § 103(m)
   ,
   Sept. 13, 1960
   ,
   74 Stat. 938
   ;
   Pub. L. 89–368, title I, § 102(b)(6)
   ,
   Mar. 15, 1966
   ,
   80 Stat. 64
   ;
   Pub. L. 98–369, div. A, title IV, § 412(b)(2)
   ,
   July 18, 1984
   ,
   98 Stat. 792
   .)
   Editorial Notes
   Amendments
   1984—Subsec. (b)(3).
   Pub. L. 98–369
   struck out par. (3) referring to section 6015 for provisions relating to declarations of estimated tax on
   self-employment income.
   1966—Subsec. (b)(3).
   Pub. L. 89–368
   added par. (3).
   1960—Subsec. (b)(2).
   Pub. L. 86–778
   included Guam and American Samoa.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1984 Amendment
   Amendment by
   Pub. L. 98–369
   applicable with respect to taxable years beginning after
   Dec. 31, 1984
   , see
   section 414(a)(1) of Pub. L. 98–369
   , set out as a note under
   section 6654 of this title
   .
   Effective Date of 1966 Amendment
   Amendment by
   Pub. L. 89–368
   applicable with respect to taxable years beginning after
   December 31, 1966
   , see
   section 102(d) of Pub. L. 89–368
   , set out as a note under
   section 6654 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/