/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 232a2d04-3238-4185-9045-50bce0b5b235
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d3e5327f-f50e-4511-92b4-0ca35c125e85
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token ';'; expected command
unexpected identifier; expected 'instance'-/
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
# IRC Section 91 - Certain foreign branch losses transferred to specified 10-percent owned foreign corporations

This file formalizes IRC §91 (Certain foreign branch losses transferred to specified 10-percent owned foreign corporations).

## References
- [26 USC §91](https://www.law.cornell.edu/uscode/text/26/91)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 91 - Certain foreign branch losses transferred to specified 10-percent owned foreign corporations
   U.S. Code
   Notes
   prev
   | next
   (a)
   In general
   If a domestic corporation transfers substantially all of the assets of a foreign branch (within the meaning of section 367(a)(3)(C), as in effect before the date of the enactment of the Tax Cuts and Jobs Act) to a specified 10-percent owned foreign corporation (as defined in
   section 245A
   ) with respect to which it is a United States shareholder after such transfer, such domestic corporation shall include in gross income for the taxable year which includes such transfer an amount equal to the
   transferred loss amount
   with respect to such transfer.
   (b)
   Transferred loss amount
   For purposes of this section, the term “
   transferred loss amount
   ” means, with respect to any transfer of substantially all of the assets of a foreign branch, the excess (if any) of—
   (1)
   the sum of losses—
   (A)
   which were incurred by the foreign branch after
   December 31, 2017
   , and before the transfer, and
   (B)
   with respect to which a deduction was allowed to the taxpayer, over
   (2)
   the sum of—
   (A)
   any taxable income of such branch for a taxable year after the taxable year in which the loss was incurred and through the close of the taxable year of the transfer, and
   (B)
   any amount which is recognized under section 904(f)(3) on account of the transfer.
   (c)
   Reduction for recognized gains
   The
   transferred loss amount
   shall be reduced (but not below zero) by the amount of gain recognized by the taxpayer on account of the transfer (other than amounts taken into account under subsection (b)(2)(B)).
   (d)
   Source of income
   Amounts included in gross income under this section shall be treated as derived from sources within the United States.
   (e)
   Basis adjustments
   Consistent with such regulations or other guidance as the Secretary shall prescribe, proper adjustments shall be made in the adjusted basis of the taxpayer’s stock in the specified 10-percent owned foreign corporation to which the transfer is made, and in the transferee’s adjusted basis in the property transferred, to reflect amounts included in gross income under this section.
   (Added
   Pub. L. 115–97, title I, § 14102(d)(1)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2193
   .)
   Editorial Notes
   References in Text
   The date of the enactment of the Tax Cuts and Jobs Act, referred to in subsec. (a), probably means the date of enactment of title I of
   Pub. L. 115–97
   , which was approved
   Dec. 22, 2017
   . Prior versions of the bill that was enacted into law as
   Pub. L. 115–97
   included such Short Title, but it was not enacted as part of title I of
   Pub. L. 115–97
   .
   Statutory Notes and Related Subsidiaries
   Effective Date
   Pub. L. 115–97, title I, § 14102(d)(3)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2194
   , provided that:
   “The amendments made by this subsection [enacting this section] shall apply to transfers after
   December 31, 2017
   .”
   Transition Rule
   Pub. L. 115–97, title I, § 14102(d)(4)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2194
   , provided that:
   “The amount of gain taken into account under section 91(c) of the
   Internal Revenue Code of 1986
   , as added by this subsection, shall be reduced by the amount of gain which would be recognized under section 367(a)(3)(C) (determined without regard to the amendments made by subsection (e) [amending
   section 367 of this title
   ]) with respect to losses incurred before
   January 1, 2018
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/