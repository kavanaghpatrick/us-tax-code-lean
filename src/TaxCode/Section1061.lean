/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ad2e9d96-5636-47a6-8ea5-30348dfa9594
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
# IRC Section 1061 - Partnership interests held in connection with performance of services

This file formalizes IRC §1061 (Partnership interests held in connection with performance of services).

## References
- [26 USC §1061](https://www.law.cornell.edu/uscode/text/26/1061)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1061 - Partnership interests held in connection with performance of services
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   In general
   If one or more
   applicable partnership interests
   are held by a taxpayer at any time during the taxable year, the excess (if any) of—
   (1)
   the taxpayer’s net long-term capital gain with respect to such interests for such taxable year, over
   (2)
   the taxpayer’s net long-term capital gain with respect to such interests for such taxable year computed by applying paragraphs (3) and (4) of sections
   [1]
   1222 by substituting “3 years” for “1 year”,
   shall be treated as short-term capital gain, notwithstanding
   section 83
   or any election in effect under section 83(b).
   (b)
   Special rule
   To the extent provided by the Secretary, subsection (a) shall not apply to income or gain attributable to any asset not held for portfolio investment on behalf of
   third party investors
   .
   (c)
   Applicable partnership interest
   For purposes of this section—
   (1)
   In general
   Except as provided in this paragraph or paragraph (4), the term “
   applicable partnership interest
   ” means any interest in a partnership which, directly or indirectly, is transferred to (or is held by) the taxpayer in connection with the performance of substantial services by the taxpayer, or any other related person, in any
   applicable trade or business.
   The previous sentence shall not apply to an interest held by a person who is employed by another entity that is conducting a trade or business (other than an
   applicable trade or business)
   and only provides services to such other entity.
   (2)
   Applicable trade or business
   The term “
   applicable trade or business
   ” means any activity conducted on a regular, continuous, and substantial basis which, regardless of whether the activity is conducted in one or more entities, consists, in whole or in part, of—
   (A)
   raising or returning capital, and
   (B)
   either—
   (i)
   investing in (or disposing of)
   specified assets
   (or identifying
   specified assets
   for such investing or
   disposition)
   , or
   (ii)
   developing
   specified assets
   .
   (3)
   Specified asset
   The term “
   specified asset
   ” means securities (as defined in section 475(c)(2) without regard to the last sentence thereof), commodities (as defined in section 475(e)(2)), real estate held for rental or investment, cash or cash equivalents, options or derivative contracts with respect to any of the foregoing, and an interest in a partnership to the extent of the partnership’s proportionate interest in any of the foregoing.
   (4)
   Exceptions
   The term “
   applicable partnership interest
   ” shall not include—
   (A)
   any interest in a partnership directly or indirectly held by a corporation, or
   (B)
   any capital interest in the partnership which provides the taxpayer with a right to share in partnership capital commensurate with—
   (i)
   the amount of capital contributed (determined at the time of receipt of such partnership interest), or
   (ii)
   the value of such interest subject to tax under
   section 83
   upon the receipt or vesting of such interest.
   (5)
   Third party investor
   The term “
   third party investor
   ” means a person who—
   (A)
   holds an interest in the partnership which does not constitute property held in connection with an
   applicable trade or business
   ; and
   (B)
   is not (and has not been) actively engaged, and is (and was) not related to a person so engaged, in (directly or indirectly) providing substantial services described in paragraph (1) for such partnership or any
   applicable trade or business
   .
   (d)
   Transfer of applicable partnership interest to related person
   (1)
   In general
   If a taxpayer transfers any
   applicable partnership interest
   , directly or indirectly, to a person related to the taxpayer, the taxpayer shall include in gross income (as short term capital gain) the excess (if any) of—
   (A)
   so much of the taxpayer’s long-term capital gains with respect to such interest for such taxable year attributable to the sale or exchange of any asset held for not more than 3 years as is allocable to such interest, over
   (B)
   any amount treated as short term capital gain under subsection (a) with respect to the transfer of such interest.
   (2)
   Related person
   For purposes of this paragraph, a person is related to the taxpayer if—
   (A)
   the person is a member of the taxpayer’s family within the meaning of section 318(a)(1), or
   (B)
   the person performed a service within the current calendar year or the preceding three calendar years in any
   applicable trade or business
   in which or for which the taxpayer performed a service.
   (e)
   Reporting
   The Secretary shall require such reporting (at the time and in the manner prescribed by the Secretary) as is necessary to carry out the purposes of this section.
   (f)
   Regulations
   The Secretary shall issue such regulations or other guidance as is necessary or appropriate to carry out the purposes of this section
   [2]
   (Added
   Pub. L. 115–97, title I, § 13309(a)(2)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2130
   .)
   [1]
   So in original. Probably should be “section”.
   [2]
   So in original. Probably should be followed by a period.
   Editorial Notes
   Prior Provisions
   A prior
   section 1061
   was renumbered
   section 1063 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date
   Pub. L. 115–97, title I, § 13309(c)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2131
   , provided that:
   “The amendments made by this section [enacting this section and renumbering former
   section 1061 of this title
   as section 1062] shall apply to taxable years beginning after
   December 31, 2017
   .”
   CFR Title
   Parts
   26
   1
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/