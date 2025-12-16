/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 62266b2c-19b8-4776-adc0-2eddb362c7f2
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
# IRC Section 2058 - State death taxes

This file formalizes IRC §2058 (State death taxes).

## References
- [26 USC §2058](https://www.law.cornell.edu/uscode/text/26/2058)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2058 - State death taxes
   U.S. Code
   Notes
   prev
   | next
   (a)
   Allowance of deduction
   For purposes of the tax imposed by section 2001, the value of the taxable estate shall be determined by deducting from the value of the gross estate the amount of any estate, inheritance, legacy, or succession taxes actually paid to any State or the District of Columbia, in respect of any property included in the gross estate (not including any such taxes paid with respect to the estate of a person other than the decedent).
   (b)
   Period of limitations
   The deduction allowed by this section shall include only such taxes as were actually paid and deduction therefor claimed before the later of—
   (1)
   4 years after the filing of the return required by section 6018, or
   (2)
   if—
   (A)
   a petition for redetermination of a deficiency has been filed with the Tax Court within the time prescribed in section 6213(a), the expiration of 60 days after the decision of the Tax Court becomes final,
   (B)
   an extension of time has been granted under section 6161 or 6166 for payment of the tax shown on the return, or of a deficiency, the date of the expiration of the period of the extension, or
   (C)
   a claim for refund or credit of an overpayment of tax imposed by this chapter has been filed within the time prescribed in section 6511, the latest of the expiration of—
   (i)
   60 days from the date of mailing by certified mail or registered mail by the Secretary to the taxpayer of a notice of the disallowance of any part of such claim,
   (ii)
   60 days after a decision by any court of competent jurisdiction becomes final with respect to a timely suit instituted upon such claim, or
   (iii)
   2 years after a notice of the waiver of disallowance is filed under section 6532(a)(3).
   Notwithstanding sections 6511 and 6512, refund based on the deduction may be made if the claim for refund is filed within the period provided in the preceding sentence. Any such refund shall be made without interest.
   (Added
   Pub. L. 107–16, title V, § 532(b)
   ,
   June 7, 2001
   ,
   115 Stat. 73
   .)
   Statutory Notes and Related Subsidiaries
   Effective Date
   Section applicable to estates of decedents dying, and generation-skipping transfers, after
   Dec. 31, 2004
   , see
   section 532(d) of Pub. L. 107–16
   , set out as an Effective Date of 2001 Amendment note under
   section 2012 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/