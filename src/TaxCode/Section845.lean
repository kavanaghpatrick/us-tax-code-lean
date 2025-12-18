/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 45c854f0-08be-412c-babc-9652354d0def
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
# IRC Section 845 - Certain reinsurance agreements

This file formalizes IRC §845 (Certain reinsurance agreements).

## References
- [26 USC §845](https://www.law.cornell.edu/uscode/text/26/845)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 845 - Certain reinsurance agreements
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   Allocation in case of reinsurance agreement involving tax avoidance or evasion
   In the case of 2 or more related persons (within the meaning of section 482) who are parties to a reinsurance agreement (or where one of the parties to a reinsurance agreement is, with respect to any contract covered by the agreement, in effect an agent of another party to such agreement or a conduit between related persons), the Secretary may—
   (1)
   allocate between or among such persons income (whether investment income, premium, or otherwise), deductions, assets, reserves, credits, and other items related to such agreement,
   (2)
   recharacterize any such items, or
   (3)
   make any other adjustment,
   if he determines that such allocation, recharacterization, or adjustment is necessary to reflect the proper amount, source, or character of the taxable income (or any item described in paragraph (1) relating to such taxable income) of each such person.
   (b)
   Reinsurance contract having significant tax avoidance effect
   If the Secretary determines that any reinsurance contract has a significant tax avoidance effect on any party to such contract, the Secretary may make proper adjustments with respect to such party to eliminate such tax avoidance effect (including treating such contract with respect to such party as terminated on December 31 of each year and reinstated on January 1 of the next year).
   (Added
   Pub. L. 98–369, div. A, title II, § 212(a)
   ,
   July 18, 1984
   ,
   98 Stat. 757
   ; amended
   Pub. L. 108–357, title VIII, § 803(a)
   ,
   Oct. 22, 2004
   ,
   118 Stat. 1569
   .)
   Editorial Notes
   Amendments
   2004—Subsec. (a).
   Pub. L. 108–357
   substituted “amount, source, or character” for “source and character” in concluding provisions.
   Statutory Notes and Related Subsidiaries
   Effective Date of 2004 Amendment
   Pub. L. 108–357, title VIII, § 803(b)
   ,
   Oct. 22, 2004
   ,
   118 Stat. 1569
   , provided that:
   “The amendments made by this section [amending this section] shall apply to any risk reinsured after the date of the enactment of this Act [
   Oct. 22, 2004
   ].”
   Effective Date
   Pub. L. 98–369, div. A, title II, § 217(d)
   ,
   July 18, 1984
   ,
   98 Stat. 762
   , as amended by
   Pub. L. 99–514, § 2
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2095
   , provided that:
   “(1)
   Subsection (a) of section 845 of the
   Internal Revenue Code of 1986
   [formerly I.R.C. 1954] (as added by this title) shall apply with respect to any risk reinsured on or after
   September 27, 1983
   .
   “(2)
   Subsection (b) of section 845 of such Code (as so added) shall apply with respect to risks reinsured after
   December 31, 1984
   .”
   CFR Title
   Parts
   26
   1
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/