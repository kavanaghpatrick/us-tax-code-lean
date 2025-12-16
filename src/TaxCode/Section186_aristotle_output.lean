/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d3dd6d32-3b9f-4094-8ad0-5815a6c3e765
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
# IRC Section 186 - Recoveries of damages for antitrust violations, etc.

This file formalizes IRC §186 (Recoveries of damages for antitrust violations, etc.).

## References
- [26 USC §186](https://www.law.cornell.edu/uscode/text/26/186)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 186 - Recoveries of damages for antitrust violations, etc.
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Allowance of deduction
   If a
   compensatory amount
   which is included in gross income is received or accrued during the taxable year for a
   compensable injury,
   there shall be allowed as a deduction for the taxable year an amount equal to the lesser of—
   (1)
   the amount of such
   compensatory amount
   , or
   (2)
   the amount of the unrecovered losses sustained as a result of such
   compensable injury
   .
   (b)
   Compensable injury
   For purposes of this section, the term “
   compensable injury
   ” means—
   (1)
   injuries sustained as a result of an infringement of a patent issued by the United States,
   (2)
   injuries sustained as a result of a breach of contract or a breach of fiduciary duty or relationship, or
   (3)
   injuries sustained in business, or to property, by reason of any conduct forbidden in the antitrust laws for which a civil action may be brought under section 4 of the Act entitled “An Act to supplement existing laws against unlawful restraints and monopolies, and for other purposes”, approved
   October 15, 1914
   (commonly known as the Clayton Act).
   (c)
   Compensatory amount
   For purposes of this section, the term “
   compensatory amount
   ” means the amount received or accrued during the taxable year as damages as a result of an award in, or in settlement of, a civil action for recovery for a
   compensable injury,
   reduced by any amounts paid or incurred in the taxable year in securing such award or settlement.
   (d)
   Unrecovered losses
   (1)
   In general
   For purposes of this section, the amount of any unrecovered loss sustained as a result of any
   compensable injury
   is—
   (A)
   the sum of the amount of the net operating losses (as determined under
   section 172
   ) for each taxable year in whole or in part within the injury period, to the extent that such net operating losses are attributable to such
   compensable injury,
   reduced by
   (B)
   the sum of—
   (i)
   the amount of the net operating losses described in subparagraph (A) which were allowed for any prior taxable year as a deduction under
   section 172
   as a net operating loss carryback or carryover to such taxable year, and
   (ii)
   the amounts allowed as a deduction under subsection (a) for any prior taxable year for prior recoveries of
   compensatory amounts
   for such
   compensable injury.
   (2)
   Injury period
   For purposes of paragraph (1), the injury period is—
   (A)
   with respect to any infringement of a patent, the period in which such infringement occurred,
   (B)
   with respect to a breach of contract or breach of fiduciary duty or relationship, the period during which amounts would have been received or accrued but for the breach of contract or breach of fiduciary duty or relationship, and
   (C)
   with respect to injuries sustained by reason of any conduct forbidden in the antitrust laws, the period in which such injuries were sustained.
   (3)
   Net operating losses attributable to compensable injuries
   For purposes of paragraph (1)—
   (A)
   a net operating loss for any taxable year shall be treated as attributable to a
   compensable injury
   to the extent of the
   compensable injury
   sustained during such taxable year, and
   (B)
   if only a portion of a net operating loss for any taxable year is attributable to a
   compensable injury
   , such portion shall (in applying
   section 172
   for purposes of this section) be considered to be a separate net operating loss for such year to be applied after the other portion of such net operating loss.
   (e)
   Effect on net operating loss carryovers
   If for the taxable year in which a
   compensatory amount
   is received or accrued any portion of a net operating loss carryover to such year is attributable to the
   compensable injury
   for which such amount is received or accrued, such portion of such net operating loss carryover shall be reduced by an amount equal to—
   (1)
   the deduction allowed under subsection (a) with respect to such
   compensatory amount
   , reduced by
   (2)
   any portion of the unrecovered losses sustained as a result of the
   compensable injury
   with respect to which the period for carryover under
   section 172
   has expired.
   (Added
   Pub. L. 91–172, title IX, § 904(a)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 711
   .)
   Editorial Notes
   References in Text
   Section 4 of the Clayton Act, referred to in subsec. (b)(3), is classified to
   section 15 of Title 15
   .
   Statutory Notes and Related Subsidiaries
   Effective Date
   Pub. L. 91–172, title IX, § 904(c)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 712
   , provided that:
   “The amendments made by this section [enacting this section] shall apply to taxable years beginning after
   December 31, 1968
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/