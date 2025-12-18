/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9021aba5-e025-415c-a8b5-109853dc7a91
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
# IRC Section 1552 - Earnings and profits

This file formalizes IRC §1552 (Earnings and profits).

## References
- [26 USC §1552](https://www.law.cornell.edu/uscode/text/26/1552)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1552 - Earnings and profits
   U.S. Code
   Notes
   prev
   | next
   (a)
   General rule
   Pursuant to regulations prescribed by the Secretary the earnings and profits of each member of an affiliated group required to be included in a consolidated return for such group filed for a taxable year shall be determined by allocating the tax liability of the group for such year among the members of the group in accord with whichever of the following methods the group shall elect in its first consolidated return filed for such a taxable year:
   (1)
   The tax liability shall be apportioned among the members of the group in accordance with the ratio which that portion of the consolidated taxable income attributable to each member of the group having taxable income bears to the consolidated taxable income.
   (2)
   The tax liability of the group shall be allocated to the several members of the group on the basis of the percentage of the total tax which the tax of such member if computed on a separate return would bear to the total amount of the taxes for all members of the group so computed.
   (3)
   The tax liability of the group (excluding the tax increases arising from the consolidation) shall be allocated on the basis of the contribution of each member of the group to the consolidated taxable income of the group. Any tax increases arising from the consolidation shall be distributed to the several members in direct proportion to the reduction in tax liability resulting to such members from the filing of the consolidated return as measured by the difference between their tax liabilities determined on a separate return basis and their tax liabilities based on their contributions to the consolidated taxable income.
   (4)
   The tax liability of the group shall be allocated in accord with any other method selected by the group with the approval of the Secretary.
   (b)
   Failure to elect
   If no election is made in such first return, the tax liability shall be allocated among the several members of the group pursuant to the method prescribed in subsection (a)(1).
   (Aug. 16, 1954, ch. 736,
   68A Stat. 371
   ;
   Pub. L. 88–272, title II, § 234(b)(8)
   ,
   Feb. 26, 1964
   ,
   78 Stat. 116
   ;
   Pub. L. 94–455, title XIX
   , §§ 1901(a)(159), 1906(b)(13)(A),
   Oct. 4, 1976
   ,
   90 Stat. 1790
   , 1834.)
   Editorial Notes
   Amendments
   1976—Subsec. (a).
   Pub. L. 94–455
   , §§ 1901(a)(159), 1906(b)(13)(A), struck out “beginning after
   December 31, 1953
   , and ending after the date of enactment of this title” after “group filed for a taxable year”, and “or his delegate” after “Secretary” in two places.
   1964—Subsec. (a)(3).
   Pub. L. 88–272
   struck out “(determined without regard to the 2 percent increase provided by section 1503(a))”, before “based on their contributions”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1976 Amendment
   Amendment by
   section 1901(a)(159) of Pub. L. 94–455
   applicable with respect to taxable years beginning after
   Dec. 31, 1976
   , see
   section 1901(d) of Pub. L. 94–455
   , set out as a note under
   section 2 of this title
   .
   Effective Date of 1964 Amendment
   Amendment by
   Pub. L. 88–272
   applicable to taxable years beginning after
   Dec. 31, 1963
   , see
   section 234(c) of Pub. L. 88–272
   , set out as a note under
   section 1503 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/