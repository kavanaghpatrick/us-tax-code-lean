/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d1bed0c9-ec45-4807-8369-4bde135d1259
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
# IRC Section 1053 - Property acquired before March 1, 1913

This file formalizes IRC §1053 (Property acquired before March 1, 1913).

## References
- [26 USC §1053](https://www.law.cornell.edu/uscode/text/26/1053)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1053 - Property acquired before March 1, 1913
   U.S. Code
   Notes
   prev
   |
   next
   In the case of property acquired before
   March 1, 1913
   , if the basis otherwise determined under this subtitle, adjusted (for the period before
   March 1, 1913
   ) as provided in section 1016, is less than the fair market value of the property as of
   March 1, 1913
   , then the basis for determining gain shall be such fair market value. In determining the fair market value of stock in a corporation as of
   March 1, 1913
   , due regard shall be given to the fair market value of the assets of the corporation as of that date.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 311
   ;
   Pub. L. 85–866, title I, § 47
   ,
   Sept. 2, 1958
   ,
   72 Stat. 1642
   .)
   Editorial Notes
   Amendments
   1958—
   Pub. L. 85–866
   substituted “subtitle” for “part”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1958 Amendment
   Amendment by
   Pub. L. 85–866
   applicable to taxable years beginning after
   Dec. 31, 1953
   , and ending after
   Aug. 16, 1954
   , see
   section 1(c)(1) of Pub. L. 85–866
   , set out as a note under
   section 165 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/