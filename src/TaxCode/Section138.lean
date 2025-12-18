/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ab1f9245-9d14-47d7-9e5c-7d7406d801d8
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 471191a0-e56e-49a6-a6bf-0b204b0f63a4
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
# IRC Section 138 - Medicare Advantage MSA

This file formalizes IRC §138 (Medicare Advantage MSA).

## References
- [26 USC §138](https://www.law.cornell.edu/uscode/text/26/138)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 138 - Medicare Advantage MSA
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Exclusion
   Gross income shall not include any payment to the
   Medicare
   Advantage MSA of an individual by the Secretary of Health and Human Services under part C of title XVIII of the
   Social Security Act
   .
   (b)
   Medicare
   Advantage MSA
   For purposes of this section, the term “
   Medicare
   Advantage MSA” means an Archer MSA (as defined in
   section 220(d)
   )—
   (1)
   which is designated as a
   Medicare
   Advantage MSA,
   (2)
   with respect to which no contribution may be made other than—
   (A)
   a contribution made by the Secretary of Health and Human Services pursuant to part C of title XVIII of the
   Social Security Act
   , or
   (B)
   a trustee-to-trustee transfer described in subsection (c)(4),
   (3)
   the governing instrument of which provides that trustee-to-trustee transfers described in subsection (c)(4) may be made to and from such account, and
   (4)
   which is established in connection with an MSA plan described in section 1859(b)(3) of the
   Social Security Act
   .
   (c)
   Special rules for distributions
   (1)
   Distributions for qualified medical expenses
   In applying
   section 220
   to a
   Medicare
   Advantage MSA—
   (A)
   qualified medical expenses shall not include amounts paid for medical care for any individual other than the account holder, and
   (B)
   section 220(d)(2)(C)
   shall not apply.
   (2)
   Penalty for distributions from
   Medicare
   Advantage MSA not used for qualified medical expenses if minimum balance not maintained
   (A)
   In general
   The tax imposed by this chapter for any taxable year in which there is a payment or distribution from a
   Medicare
   Advantage MSA which is not used exclusively to pay the qualified medical expenses of the account holder shall be increased by 50 percent of the excess (if any) of—
   (i)
   the amount of such payment or distribution, over
   (ii)
   the excess (if any) of—
   (I)
   the fair market value of the assets in such MSA as of the close of the calendar year preceding the calendar year in which the taxable year begins, over
   (II)
   an amount equal to 60 percent of the deductible under the
   Medicare
   Advantage MSA plan covering the account holder as of January 1 of the calendar year in which the taxable year begins.
   Section 220(f)(4)
   shall not apply to any payment or distribution from a
   Medicare
   Advantage MSA.
   (B)
   Exceptions
   Subparagraph (A) shall not apply if the payment or distribution is made on or after the date the account holder—
   (i)
   becomes disabled within the meaning of section 72(m)(7), or
   (ii)
   dies.
   (C)
   Special rules
   For purposes of subparagraph (A)—
   (i)
   all
   Medicare
   Advantage MSAs of the account holder shall be treated as 1 account,
   (ii)
   all payments and distributions not used exclusively to pay the qualified medical expenses of the account holder during any taxable year shall be treated as 1 distribution, and
   (iii)
   any distribution of property shall be taken into account at its fair market value on the date of the distribution.
   (3)
   Withdrawal of erroneous contributions
   Section 220(f)(2) and paragraph (2) of this subsection shall not apply to any payment or distribution from a
   Medicare
   Advantage MSA to the Secretary of Health and Human Services of an erroneous contribution to such MSA and of the net income attributable to such contribution.
   (4)
   Trustee-to-trustee transfers
   Section 220(f)(2) and paragraph (2) of this subsection shall not apply to any trustee-to-trustee transfer from a
   Medicare
   Advantage MSA of an account holder to another
   Medicare
   Advantage MSA of such account holder.
   (d)
   Special rules for treatment of account after death of account holder
   In applying section 220(f)(8)(A) to an account which was a
   Medicare
   Advantage MSA of a decedent, the rules of section 220(f) shall apply in lieu of the rules of subsection (c) of this section with respect to the spouse as the account holder of such
   Medicare
   Advantage MSA.
   (e)
   Reports
   In the case of a
   Medicare
   Advantage MSA, the report under
   section 220(h)
   —
   (1)
   shall include the fair market value of the assets in such
   Medicare
   Advantage MSA as of the close of each calendar year, and
   (2)
   shall be furnished to the account holder—
   (A)
   not later than January 31 of the calendar year following the calendar year to which such reports relate, and
   (B)
   in such manner as the Secretary prescribes in such regulations.
   (f)
   Coordination with limitation on number of taxpayers having Archer MSAs
   Subsection (i) of
   section 220
   shall not apply to an individual with respect to a
   Medicare
   Advantage MSA, and
   Medicare
   Advantage MSAs shall not be taken into account in determining whether the numerical limitations under section 220(j) are exceeded.
   (Added
   Pub. L. 105–33, title IV, § 4006(a)
   ,
   Aug. 5, 1997
   ,
   111 Stat. 332
   ; amended
   Pub. L. 106–554, § 1(a)(7) [title II, § 202(a)(3), (b)(6), (10)]
   ,
   Dec. 21, 2000
   ,
   114 Stat. 2763
   , 2763A–628, 2763A–629;
   Pub. L. 108–311, title IV, § 408(a)(5)(A)
   –(F),
   Oct. 4, 2004
   ,
   118 Stat. 1191
   .)
   Editorial Notes
   References in Text
   The
   Social Security Act
   , referred to in subsecs. (a) and (b)(2)(A), is act Aug. 14, 1935, ch. 531,
   49 Stat. 620
   . Part C of title XVIII of the Act is classified generally to part C (§ 1395w–21 et seq.) of subchapter XVIII of chapter 7 of Title 42, The Public Health and Welfare. Section 1859 of the Act is classified to
   section 1395w–28 of Title 42
   . For complete classification of this Act to the Code, see
   section 1305 of Title 42
   and Tables.
   Prior Provisions
   A prior
   section 138
   was renumbered
   section 140 of this title
   .
   Amendments
   2004—
   Pub. L. 108–311, § 408(a)(5)(A)
   –(D), substituted “
   Medicare
   Advantage” for “
   Medicare
   +Choice” wherever appearing in section catchline, headings, and text.
   Subsec. (c)(2)(C)(i).
   Pub. L. 108–311, § 408(a)(5)(E)
   , substituted “
   Medicare
   Advantage MSAs” for “
   Medicare
   +Choice MSAs”.
   Subsec. (f).
   Pub. L. 108–311, § 408(a)(5)(F)
   , substituted “
   Medicare
   Advantage MSAs” for “
   Medicare
   +Choice MSA’s”.
   2000—Subsec. (b).
   Pub. L. 106–554, § 1(a)(7) [title II, § 202(b)(10)]
   , substituted “an Archer MSA” for “a Archer MSA” in introductory provisions.
   Pub. L. 106–554, § 1(a)(7) [title II, § 202(a)(3)]
   , substituted “Archer MSA” for “medical savings account” in introductory provisions.
   Subsec. (f).
   Pub. L. 106–554, § 1(a)(7) [title II, § 202(b)(6)]
   , substituted “Archer MSAs” for “medical savings accounts” in heading.
   Statutory Notes and Related Subsidiaries
   Effective Date
   Pub. L. 105–33, title IV, § 4006(c)
   ,
   Aug. 5, 1997
   ,
   111 Stat. 334
   , provided that:
   “The amendments made by this section [enacting this section, amending sections
   220
   and
   4973
   of this title, and renumbering former
   section 138 of this title
   as
   section 139 of this title
   ] shall apply to taxable years beginning after
   December 31, 1998
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/