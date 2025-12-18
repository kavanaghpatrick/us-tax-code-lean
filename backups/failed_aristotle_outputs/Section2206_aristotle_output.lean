/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0279d702-846e-4ed6-bbb8-506bcafc471a
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
# IRC Section 2206 - Liability of life insurance beneficiaries

This file formalizes IRC §2206 (Liability of life insurance beneficiaries).

## References
- [26 USC §2206](https://www.law.cornell.edu/uscode/text/26/2206)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2206 - Liability of life insurance beneficiaries
   U.S. Code
   Notes
   prev
   |
   next
   Unless the decedent directs otherwise in his will, if any part of the gross estate on which tax has been paid consists of proceeds of policies of insurance on the life of the decedent receivable by a beneficiary other than the
   executor
   , the
   executor
   shall be entitled to recover from such beneficiary such portion of the total tax paid as the proceeds of such policies bear to the taxable estate. If there is more than one such beneficiary, the
   executor
   shall be entitled to recover from such beneficiaries in the same ratio. In the case of such proceeds receivable by the surviving spouse of the decedent for which a deduction is allowed under section 2056 (relating to marital deduction), this section shall not apply to such proceeds except as to the amount thereof in excess of the aggregate amount of the marital deductions allowed under such section.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 402
   ;
   Pub. L. 94–455, title XX, § 2001(c)(1)(H)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1852
   .)
   Editorial Notes
   Amendments
   1976—
   Pub. L. 94–455
   substituted “the taxable estate” for “the sum of the taxable estate and the amount of the exemption allowed in computing the taxable estate, determined under section 2051” after “policies bear to”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1976 Amendment
   Amendment by
   Pub. L. 94–455
   applicable to estates of decedents dying after
   Dec. 31, 1976
   , see
   section 2001(d)(1) of Pub. L. 94–455
   , set out as a note under
   section 2001 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/