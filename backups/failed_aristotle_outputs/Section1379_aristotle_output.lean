/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 24679f00-b005-4615-a973-4fd89176201a
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
# IRC Section 1379 - Transitional rules on enactment

This file formalizes IRC §1379 (Transitional rules on enactment).

## References
- [26 USC §1379](https://www.law.cornell.edu/uscode/text/26/1379)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1379 - Transitional rules on enactment
   U.S. Code
   Notes
   prev
   | next
   (a)
   Old elections
   Any election made under section 1372(a) (as in effect before the enactment of the
   Subchapter S Revision Act of 1982
   ) shall be treated as an election made under section 1362.
   (b)
   References to prior law included
   Any references in this title to a provision of this subchapter shall, to the extent not inconsistent with the purposes of this subchapter, include a reference to the corresponding provision as in effect before the enactment of the
   Subchapter S Revision Act of 1982
   .
   (c)
   Distributions of undistributed taxable income
   If a corporation was an electing
   small business corporation
   for the
   last preenactment year
   , subsections (f) and (d) of section 1375 (as in effect before the enactment of the
   Subchapter S Revision Act of 1982
   ) shall continue to apply with respect to distributions of undistributed taxable income for any taxable year beginning before
   January 1, 1983
   .
   (d)
   Carryforwards
   If a corporation was an electing
   small business corporation
   for the
   last preenactment year
   and is an S corporation for the
   1st postenactment year
   , any carryforward to the 1st post­enactment year which arose in a taxable year for which the corporation was an electing
   small business corporation
   shall be treated as arising in the
   1st postenactment year
   .
   (e)
   Preenactment and postenactment years defined
   For purposes of this subsection—
   (1)
   Last preenactment year
   The term “
   last preenactment year
   ” means the last taxable year of a corporation which begins before
   January 1, 1983
   .
   (2)
   1st postenactment year
   The term “
   1st postenactment year
   ” means the 1st taxable year of a corporation which begins after
   December 31, 1982
   .
   (Added
   Pub. L. 97–354, § 2
   ,
   Oct. 19, 1982
   ,
   96 Stat. 1686
   ; amended
   Pub. L. 98–369, div. A, title VII, § 721(n)
   ,
   July 18, 1984
   ,
   98 Stat. 969
   .)
   Editorial Notes
   References in Text
   The enactment of the
   Subchapter S Revision Act of 1982
   , referred to in subsecs. (a) to (c), is the enactment of
   Pub. L. 97–354
   , which was approved
   Oct. 19, 1982
   .
   Prior Provisions
   A prior section 1379, added
   Pub. L. 91–172, title V, § 531(a)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 654
   ; amended
   Pub. L. 93–406, title II, § 2001(b)
   ,
   Sept. 2, 1974
   ,
   88 Stat. 952
   ;
   Pub. L. 97–34, title III, § 312(c)(6)
   ,
   Aug. 13, 1981
   ,
   95 Stat. 284
   ;
   Pub. L. 97–248, title II, § 238(c)
   ,
   Sept. 3, 1982
   ,
   96 Stat. 513
   , related to certain qualified pension, etc., plans, prior to the general revision of this subchapter by
   section 2 of Pub. L. 97–354
   .
   Amendments
   1984—Subsec. (b).
   Pub. L. 98–369
   struck out “In applying this subchapter to any taxable year beginning after
   December 31, 1982
   ,” and substituted “Any references in this title to a provision” for “any reference in this subchapter to another provision”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1984 Amendment
   Amendment by
   Pub. L. 98–369
   effective as if included in
   Subchapter S Revision Act of 1982
   ,
   Pub. L. 97–354
   , see
   section 721(y)(1) of Pub. L. 98–369
   , set out as a note under
   section 1361 of this title
   .
   Effective Date
   Section applicable to taxable years beginning after
   Dec. 31, 1983
   , except that this section as in effect before
   Oct. 19, 1982
   , to remain in effect for years beginning before
   Jan. 1, 1984
   , see section 6(a), (b)(1) of
   Pub. L. 97–354
   , set out as a note under
   section 1361 of this title
   .
   Coordination of Repeals of Certain Sections
   Subsec. (b) of this section as in effect on day before
   Sept. 3, 1982
   , inapplicable to any
   section 401(j)
   plan, see
   section 713(d)(8) of Pub. L. 98–369
   , set out as a note under
   section 404 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/