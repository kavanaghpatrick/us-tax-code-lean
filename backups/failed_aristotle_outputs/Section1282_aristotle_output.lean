/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8f953ecb-6a09-4d84-900a-2dc82b215b07
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
# IRC Section 1282 - Deferral of interest deduction allocable to accrued discount

This file formalizes IRC §1282 (Deferral of interest deduction allocable to accrued discount).

## References
- [26 USC §1282](https://www.law.cornell.edu/uscode/text/26/1282)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1282 - Deferral of interest deduction allocable to accrued discount
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   Except as otherwise provided in this section, the net direct interest expense with respect to any
   short-term obligation
   shall be allowed as a deduction for the taxable year only to the extent such expense exceeds the sum of—
   (1)
   the daily portions of the
   acquisition discount
   for each day during the taxable year on which the taxpayer held such obligation, and
   (2)
   the amount of any interest payable on the obligation (other than interest taken into account in determining the amount of the
   acquisition discount
   ) which accrues during the taxable year while the taxpayer held such obligation (and is not included in the gross income of the taxpayer for such taxable year by reason of the taxpayer’s method of accounting).
   (b)
   Section not to apply to obligations to which
   section 1281
   applies
   (1)
   In general
   This section shall not apply to any
   short-term obligation
   to which
   section 1281
   applies.
   (2)
   Election to have
   section 1281
   apply to all obligations
   (A)
   In general
   A taxpayer may make an election under this paragraph to have section 1281 apply to all
   short-term obligations
   acquired by the taxpayer on or after the 1st day of the 1st taxable year to which such election applies.
   (B)
   Period to which election applies
   An election under this paragraph shall apply to the taxable year for which it is made and for all subsequent taxable years, unless the taxpayer secures the consent of the Secretary to the revocation of such election.
   (c)
   Certain rules made applicable
   Rules similar to the rules of subsections (b) and (c) of
   section 1277
   shall apply for purposes of this section.
   (d)
   Cross reference
   For special rules limiting the application of this section to
   original issue discount
   in the case of nongovernmental obligations, see section 1283(c).
   (Added
   Pub. L. 98–369, div. A, title I, § 41(a)
   ,
   July 18, 1984
   ,
   98 Stat. 549
   ; amended
   Pub. L. 99–514, title XVIII, § 1803(a)(8)(B)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2794
   .)
   Editorial Notes
   Amendments
   1986—Subsec. (a).
   Pub. L. 99–514
   amended subsec. (a) generally, designating existing provisions as par. (1) and adding par. (2).
   Statutory Notes and Related Subsidiaries
   Effective Date of 1986 Amendment
   Amendment by
   Pub. L. 99–514
   effective, except as otherwise provided, as if included in the provisions of the
   Tax Reform Act of 1984
   ,
   Pub. L. 98–369, div. A
   , to which such amendment relates, see
   section 1881 of Pub. L. 99–514
   , set out as a note under
   section 48 of this title
   .
   Effective Date
   Section applicable to taxable years ending after
   July 18, 1984
   , and to obligations acquired after that date, see
   section 44 of Pub. L. 98–369
   , set out as a note under
   section 1271 of this title
   .
   Plan Amendments Not Required Until January 1, 1989
   For provisions directing that if any amendments made by subtitle A or subtitle C of title XI [§§
   1101–1147
   and
   1171–1177
   ] or title XVIII [§§ 1800–1899A] of
   Pub. L. 99–514
   require an amendment to any plan, such plan amendment shall not be required to be made before the first plan year beginning on or after
   Jan. 1, 1989
   , see
   section 1140 of Pub. L. 99–514
   , as amended, set out as a note under
   section 401 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/