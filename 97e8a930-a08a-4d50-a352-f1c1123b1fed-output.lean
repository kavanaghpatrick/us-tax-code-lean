/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 97e8a930-a08a-4d50-a352-f1c1123b1fed
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
# IRC Section 1353 - Notional shipping income

This file formalizes IRC §1353 (Notional shipping income).

## References
- [26 USC §1353](https://www.law.cornell.edu/uscode/text/26/1353)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1353 - Notional shipping income
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   In general
   For purposes of this subchapter, the notional shipping income of an
   electing corporation
   shall be the sum of the amounts determined under subsection (b) for each
   qualifying vessel
   operated by such
   electing corporation
   .
   (b)
   Amounts
   (1)
   In general
   For purposes of subsection (a), the amount of notional shipping income of an
   electing corporation
   for each
   qualifying vessel
   for the taxable year shall equal the product of—
   (A)
   the daily notional shipping income, and
   (B)
   the number of days during the taxable year that the
   electing corporation
   operated such vessel as a
   qualifying vessel
   in
   United States foreign trade
   .
   (2)
   Treatment of vessels the income from which is not otherwise subject to tax
   In the case of a
   qualifying vessel
   any of the income from which is not included in gross income by reason of
   section 883
   or otherwise, the amount of notional shipping income from such vessel for the taxable year shall be the amount which bears the same ratio to such shipping income (determined without regard to this paragraph) as the gross income from the operation of such vessel in the
   United States foreign trade
   bears to the sum of such gross income and the income so excluded.
   (c)
   Daily notional shipping income
   For purposes of subsection (b), the daily notional shipping income from the operation of a
   qualifying vessel
   is—
   (1)
   40 cents for each 100 tons of so much of the net tonnage of the vessel as does not exceed 25,000 net tons, and
   (2)
   20 cents for each 100 tons of so much of the net tonnage of the vessel as exceeds 25,000 net tons.
   (d)
   Multiple operators of vessel
   If for any period 2 or more persons are operators of a
   qualifying vessel
   , the notional shipping income from the operation of such vessel for such period shall be allocated among such persons on the basis of their respective ownership, charter, and operating agreement interests in such vessel or on such other basis as the Secretary may prescribe by regulations.
   (Added
   Pub. L. 108–357, title II, § 248(a)
   ,
   Oct. 22, 2004
   ,
   118 Stat. 1450
   ; amended
   Pub. L. 109–135, title IV, § 403(g)(1)(A)
   ,
   Dec. 21, 2005
   ,
   119 Stat. 2624
   .)
   Editorial Notes
   Amendments
   2005—Subsec. (d).
   Pub. L. 109–135
   substituted “ownership, charter, and operating agreement interests” for “ownership and charter interests”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 2005 Amendment
   Amendment by
   Pub. L. 109–135
   effective as if included in the provision of the
   American Jobs Creation Act of 2004
   ,
   Pub. L. 108–357
   , to which such amendment relates, see
   section 403(nn) of Pub. L. 109–135
   , set out as a note under
   section 26 of this title
   .
   Effective Date
   Section applicable to taxable years beginning after
   Oct. 22, 2004
   , see
   section 248(c) of Pub. L. 108–357
   , set out as an Effective Date of 2004 Amendments note under
   section 56 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/