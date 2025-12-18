/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bfbc140c-238c-4463-bb38-c5353b4a8815
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
# IRC Section 1373 - Foreign income

This file formalizes IRC §1373 (Foreign income).

## References
- [26 USC §1373](https://www.law.cornell.edu/uscode/text/26/1373)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1373 - Foreign income
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   S corporation treated as partnership, etc.
   For purposes of subparts A and F of part III, and part V, of subchapter N (relating to income from sources without the United States)—
   (1)
   an S corporation shall be treated as a partnership, and
   (2)
   the shareholders of such corporation shall be treated as partners of such partnership.
   (b)
   Recapture of overall foreign loss
   For purposes of section 904(f) (relating to recapture of overall foreign loss), the making or termination of an election to be treated as an S corporation shall be treated as a
   disposition
   of the business.
   (Added
   Pub. L. 97–354, § 2
   ,
   Oct. 19, 1982
   ,
   96 Stat. 1682
   .)
   Editorial Notes
   Prior Provisions
   A prior section 1373, added
   Pub. L. 85–866, title I, § 64(a)
   ,
   Sept. 2, 1958
   ,
   72 Stat. 1652
   ; amended
   Pub. L. 89–389, § 2(b)(3)
   ,
   Apr. 14, 1966
   ,
   80 Stat. 114
   ;
   Pub. L. 91–172, title III, § 301(b)(10)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 586
   , related to taxation of corporation undistributed taxable income to shareholders, prior to the general revision of this subchapter by
   section 2 of Pub. L. 97–354
   .
   Statutory Notes and Related Subsidiaries
   Effective Date
   Section applicable to taxable years beginning after
   Dec. 31, 1982
   , see
   section 6(a) of Pub. L. 97–354
   , set out as a note under
   section 1361 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/