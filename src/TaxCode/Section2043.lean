/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: be4f5d6b-fc6d-4bd5-a24c-d2c89e3fad05
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
# IRC Section 2043 - Transfers for insufficient consideration

This file formalizes IRC §2043 (Transfers for insufficient consideration).

## References
- [26 USC §2043](https://www.law.cornell.edu/uscode/text/26/2043)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2043 - Transfers for insufficient consideration
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   In general
   If any one of the transfers, trusts, interests, rights, or powers enumerated and described in sections 2035 to 2038, inclusive, and section 2041 is made, created, exercised, or relinquished for a consideration in money or money’s worth, but is not a bona fide sale for an adequate and full consideration in money or money’s worth, there shall be included in the gross estate only the excess of the fair market value at the time of death of the property otherwise to be included on account of such transaction, over the value of the consideration received therefor by the decedent.
   (b)
   Marital rights not treated as consideration
   (1)
   In general
   For purposes of this chapter, a relinquishment or promised relinquishment of dower or curtesy, or of a statutory estate created in lieu of dower or curtesy, or of other marital rights in the decedent’s property or estate, shall not be considered to any extent a consideration “in money or money’s worth”.
   (2)
   Exception
   For purposes of section 2053 (relating to expenses, indebtedness, and taxes), a transfer of property which satisfies the requirements of paragraph (1) of section 2516 (relating to certain property settlements) shall be considered to be made for an adequate and full consideration in money or money’s worth.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 388
   ;
   Pub. L. 98–369, div. A, title IV, § 425(a)(1)
   ,
   July 18, 1984
   ,
   98 Stat. 803
   .)
   Editorial Notes
   Amendments
   1984—Subsec. (b).
   Pub. L. 98–369
   amended subsec. (b) generally, designating existing provisions as par. (1) and adding par. (2).
   Statutory Notes and Related Subsidiaries
   Effective Date of 1984 Amendment
   Pub. L. 98–369, div. A, title IV, § 425(c)(1)
   ,
   July 18, 1984
   ,
   98 Stat. 804
   , provided that:
   “The amendments made by subsection (a) [amending this section and
   section 2053 of this title
   ] shall apply to estates of decedents dying after the date of the enactment of this Act [
   July 18, 1984
   ].”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/