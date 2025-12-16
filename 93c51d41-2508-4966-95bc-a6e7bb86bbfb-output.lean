/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 93c51d41-2508-4966-95bc-a6e7bb86bbfb
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
# IRC Section 277 - Deductions incurred by certain membership organizations in transactions with members

This file formalizes IRC §277 (Deductions incurred by certain membership organizations in transactions with members).

## References
- [26 USC §277](https://www.law.cornell.edu/uscode/text/26/277)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 277 - Deductions incurred by certain membership organizations in transactions with members
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   In the case of a social club or other membership organization which is operated primarily to furnish services or goods to members and which is not exempt from taxation, deductions for the taxable year attributable to furnishing services, insurance, goods, or other items of value to members shall be allowed only to the extent of income derived during such year from members or transactions with members (including income derived during such year from institutes and trade shows which are primarily for the education of members). If for any taxable year such deductions exceed such income, the excess shall be treated as a deduction attributable to furnishing services, insurance, goods, or other items of value to members paid or incurred in the succeeding taxable year. The deductions provided by sections 243 and 245 (relating to dividends received by corporations) shall not be allowed to any organization to which this section applies for the taxable year.
   (b)
   Exceptions
   Subsection (a) shall not apply to any organization—
   (1)
   which for the taxable year is subject to taxation under subchapter H or L,
   (2)
   which has made an election before
   October 9, 1969
   , under
   section 456(c)
   or which is affiliated with such an organization,
   (3)
   which for each day of any taxable year is a national securities exchange subject to regulation under the
   Securities Exchange Act of 1934
   or a contract market subject to regulation under the
   Commodity Exchange Act
   , or
   (4)
   which is engaged primarily in the gathering and distribution of news to its members for publication.
   (Added
   Pub. L. 91–172, title I, § 121(b)(3)(A)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 540
   ; amended
   Pub. L. 94–568, § 1(c)
   ,
   Oct. 20, 1976
   ,
   90 Stat. 2697
   ;
   Pub. L. 99–514, title XVI, § 1604(a)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2769
   ;
   Pub. L. 113–295, div. A, title II, § 221(a)(41)(G)
   ,
   Dec. 19, 2014
   ,
   128 Stat. 4044
   .)
   Editorial Notes
   References in Text
   The
   Securities Exchange Act of 1934
   , referred to in subsec. (b)(3), is act June 6, 1934, ch. 404,
   48 Stat. 881
   , which is classified principally to chapter 2B (§ 78a et seq.) of Title 15, Commerce and Trade. For complete classification of this Act to the Code, see
   section 78a of Title 15
   and Tables.
   The
   Commodity Exchange Act
   , referred to in subsec. (b)(3), is act Sept. 21, 1922, ch. 369,
   42 Stat. 998
   , which is classified generally to chapter 1 (§ 1 et seq.) of Title 7, Agriculture. For complete classification of this Act to the Code, see
   section 1 of Title 7
   and Tables.
   Amendments
   2014—Subsec. (a).
   Pub. L. 113–295
   struck out “, 244,” after “sections 243”.
   1986—Subsec. (b)(4).
   Pub. L. 99–514
   added par. (4).
   1976—Subsec. (a).
   Pub. L. 94–568
   provided that the deductions provided by sections 243, 244, and 245 (relating to dividends received by corporations) shall not be allowed to any organization to which this section applies for the taxable year.
   Statutory Notes and Related Subsidiaries
   Effective Date of 2014 Amendment
   Amendment by
   Pub. L. 113–295
   not applicable to preferred stock issued before
   Oct. 1, 1942
   (determined in the same manner as under
   section 247 of this title
   as in effect before its repeal by
   Pub. L. 113–295
   ), see
   section 221(a)(41)(K) of Pub. L. 113–295
   , set out as a note under
   section 172 of this title
   .
   Except as otherwise provided in
   section 221(a) of Pub. L. 113–295
   , amendment by
   Pub. L. 113–295
   effective
   Dec. 19, 2014
   , subject to a savings provision, see
   section 221(b) of Pub. L. 113–295
   , set out as a note under
   section 1 of this title
   .
   Effective Date of 1986 Amendment
   Pub. L. 99–514, title XVI, § 1604(b)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2769
   , provided that:
   “The amendment made by this section [amending this section] shall apply to taxable years beginning after the date of the enactment of this Act [
   Oct. 22, 1986
   ].”
   Effective Date of 1976 Amendment
   Amendment by
   Pub. L. 94–568
   applicable to taxable years beginning after
   Oct. 20, 1976
   , see
   section 1(d) of Pub. L. 94–568
   , set out as a note under
   section 501 of this title
   .
   Effective Date
   Section applicable to taxable years beginning after
   Dec. 31, 1970
   , see
   section 121(g) of Pub. L. 91–172
   , set out as an Effective Date of 1969 Amendment note under
   section 511 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/