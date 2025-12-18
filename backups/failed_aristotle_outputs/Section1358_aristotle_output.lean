/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 942b1c0b-c277-4746-8869-64136148e310
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
# IRC Section 1358 - Allocation of credits, income, and deductions

This file formalizes IRC §1358 (Allocation of credits, income, and deductions).

## References
- [26 USC §1358](https://www.law.cornell.edu/uscode/text/26/1358)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1358 - Allocation of credits, income, and deductions
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Qualifying shipping activities
   For purposes of this chapter, the
   qualifying shipping activities
   of an
   electing corporation
   shall be treated as a separate trade or business activity distinct from all other activities conducted by such corporation.
   (b)
   Exclusion of credits or deductions
   (1)
   No deduction shall be allowed against the notional shipping income of an
   electing corporation
   , and no credit shall be allowed against the tax imposed by section 1352(2).
   (2)
   No deduction shall be allowed for any net operating loss attributable to the
   qualifying shipping activities
   of any person to the extent that such loss is carried forward by such person from a taxable year preceding the first taxable year for which such person was an
   electing corporation.
   (c)
   Transactions not at arm’s length
   Section 482
   applies in accordance with this subsection to a transaction or series of transactions—
   (1)
   as between an
   electing corporation
   and another person, or
   (2)
   as between a person’s
   qualifying shipping activities
   and other activities carried on by it.
   (Added
   Pub. L. 108–357, title II, § 248(a)
   ,
   Oct. 22, 2004
   ,
   118 Stat. 1456
   ; amended
   Pub. L. 115–141, div. U, title IV, § 401(a)(188)
   , (189),
   Mar. 23, 2018
   ,
   132 Stat. 1193
   .)
   Editorial Notes
   Amendments
   2018—Subsec. (b)(1).
   Pub. L. 115–141, § 401(a)(188)
   , substituted “section 1352(2)” for “section 1352(a)(2)”.
   Subsec. (c)(2).
   Pub. L. 115–141, § 401(a)(189)
   , substituted “a person’s” for “an person’s”.
   Statutory Notes and Related Subsidiaries
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