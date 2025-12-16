/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a2b08ed9-a6cc-4754-842a-fc107feaf6d7
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
# IRC Section 128 - Employer contributions to Trump accounts

This file formalizes IRC §128 (Employer contributions to Trump accounts).

## References
- [26 USC §128](https://www.law.cornell.edu/uscode/text/26/128)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 128 - Employer contributions to Trump accounts
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   In general
   Gross income of an
   employee
   does not include amounts paid by the employer as a contribution to the Trump account of such
   employee
   or of any dependent of such
   employee
   if the amounts are paid or incurred pursuant to a program which is described in subsection (c).
   (b)
   Limitation
   (1)
   In general
   The amount which may be excluded under subsection (a) with respect to any
   employee
   shall not exceed $2,500.
   (2)
   Inflation adjustment
   (A)
   In general
   In the case of any taxable year beginning after 2027, the $2,500 amount in paragraph (1) shall be increased by an amount equal to—
   (i)
   such dollar amount, multiplied by
   (ii)
   the cost-of-living adjustment determined under section 1(f)(3) for the calendar year in which the taxable year begins by substituting “calendar year 2026” for “calendar year 2016” in subparagraph (A)(ii) thereof.
   (B)
   Rounding
   If any increase determined under subparagraph (A) is not a multiple of $100, such increase shall be rounded to the next lowest multiple of $100.
   (c)
   Trump account contribution program
   For purposes of this section, a Trump account contribution program is a separate written plan of an employer for the exclusive benefit of his
   employees
   to provide contributions to the Trump accounts of such
   employees
   or dependents of such
   employees
   which meets requirements similar to the requirements of paragraphs (2), (3), (6), (7), and (8) of section 129(d).
   (Added
   Pub. L. 119–21, title VII, § 70204(b)(1)
   ,
   July 4, 2025
   ,
   139 Stat. 186
   .)
   Editorial Notes
   Prior Provisions
   A prior section 128, added and amended
   Pub. L. 97–34, title III
   , §§ 301(a), 302(a), (d)(1),
   Aug. 13, 1981
   ,
   95 Stat. 267
   , 270, 274;
   Pub. L. 97–448, title I
   , §§ 103(a)(1), (5), (b), 109,
   Jan. 12, 1983
   ,
   96 Stat. 2374
   , 2375, 2391;
   Pub. L. 98–21, title I
   , §§ 121(f)(2), (g), 122(c)(3), (d),
   Apr. 20, 1983
   ,
   97 Stat. 84
   , 87;
   Pub. L. 98–369, div. A, title I, § 16(a)
   ,
   July 18, 1984
   ,
   98 Stat. 505
   , related to interest on certain savings certificates, prior to repeal by
   Pub. L. 101–508, title XI, § 11801(a)(10)
   ,
   Nov. 5, 1990
   ,
   104 Stat. 1388–520
   . For savings provision, see
   section 11821(b) of Pub. L. 101–508
   , set out as a note under
   section 45K of this title
   .
   Another prior
   section 128
   was renumbered
   section 140 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date
   Pub. L. 119–21, title VII, § 70204(e)
   ,
   July 4, 2025
   ,
   139 Stat. 188
   , provided that:
   “The amendments made by this section [enacting this section and sections
   139J
   ,
   530A
   ,
   6434
   , and
   6659
   of this title and amending sections
   529A
   ,
   4973
   ,
   6213
   , and
   6693
   of this title] shall apply to taxable years beginning after
   December 31, 2025
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/