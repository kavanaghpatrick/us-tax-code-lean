/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 46d14b3b-017e-4825-b2bf-5337937a56c8
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
# IRC Section 591 - Deduction for dividends paid on deposits

This file formalizes IRC §591 (Deduction for dividends paid on deposits).

## References
- [26 USC §591](https://www.law.cornell.edu/uscode/text/26/591)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 591 - Deduction for dividends paid on deposits
   U.S. Code
   Notes
   prev |
   next
   (a)
   In general
   In the case of
   mutual savings banks
   , cooperative banks, domestic building and loan associations, and other savings institutions chartered and supervised as savings and loan or similar associations under Federal or State law, there shall be allowed as deductions in computing taxable income amounts paid to, or credited to the accounts of, depositors or holders of accounts as dividends or interest on their deposits or withdrawable accounts, if such amounts paid or credited are withdrawable on demand subject only to customary notice of intention to withdraw.
   (b)
   Mutual savings bank to include certain banks with capital stock
   For purposes of this part, the term “
   mutual savings bank
   ” includes any bank—
   (1)
   which has capital stock represented by shares, and
   (2)
   which is subject to, and operates under, Federal or State laws relating to
   mutual savings bank
   .
   (Aug. 16, 1954, ch. 736,
   68A Stat. 204
   ;
   Pub. L. 87–834, § 6(f)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 984
   ;
   Pub. L. 97–34, title II, § 245(a)
   ,
   Aug. 13, 1981
   ,
   95 Stat. 255
   .)
   Editorial Notes
   Amendments
   1981—
   Pub. L. 97–34
   designated existing provisions as subsec. (a), inserted heading “In general”, and added subsec. (b).
   1962—
   Pub. L. 87–834
   included other savings institutions chartered and supervised as savings and loan or similar associations under Federal or State law, and authorized amounts paid as interest as a deduction.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1981 Amendment
   Pub. L. 97–34, title II, § 246(d)
   ,
   Aug. 13, 1981
   ,
   95 Stat. 256
   , provided that:
   “The amendments made by section 245 [amending this section and
   section 593 of this title
   ] shall apply with respect to taxable years ending after the date of the enactment of this Act [
   Aug. 13, 1981
   ].”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/