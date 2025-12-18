/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a3de3bb9-9b6a-4241-be12-a31daba545bc
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
# IRC Section 2207 - Liability of recipient of property over which decedent had power of appointment

This file formalizes IRC §2207 (Liability of recipient of property over which decedent had power of appointment).

## References
- [26 USC §2207](https://www.law.cornell.edu/uscode/text/26/2207)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2207 - Liability of recipient of property over which decedent had power of appointment
   U.S. Code
   Notes
   prev
   |
   next
   Unless the decedent directs otherwise in his will, if any part of the gross estate on which the tax has been paid consists of the value of property included in the gross estate under section 2041, the
   executor
   shall be entitled to recover from the person receiving such property by reason of the exercise, nonexercise, or release of a power of appointment such portion of the total tax paid as the value of such property bears to the taxable estate. If there is more than one such person, the
   executor
   shall be entitled to recover from such persons in the same ratio. In the case of such property received by the surviving spouse of the decedent for which a deduction is allowed under section 2056 (relating to marital deduction), this section shall not apply to such property except as to the value thereof reduced by an amount equal to the excess of the aggregate amount of the marital deductions allowed under section 2056 over the amount of proceeds of insurance upon the life of the decedent receivable by the surviving spouse for which proceeds a marital deduction is allowed under such section.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 402
   ;
   Pub. L. 94–455, title XX, § 2001(c)(1)(I)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1852
   .)
   Editorial Notes
   Amendments
   1976—
   Pub. L. 94–455
   substituted “the taxable estate” for “the sum of the taxable estate and the amount of the exemption allowed in computing the taxable estate, determined under section 2052, or section 2106(a), as the case may be” after “property bears to”.
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