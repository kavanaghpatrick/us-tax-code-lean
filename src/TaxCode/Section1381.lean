/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6425a032-c647-434b-99ee-0a17a7cb83ef
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
# IRC Section 1381 - Organizations to which part applies

This file formalizes IRC §1381 (Organizations to which part applies).

## References
- [26 USC §1381](https://www.law.cornell.edu/uscode/text/26/1381)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1381 - Organizations to which part applies
   U.S. Code
   Notes
   prev |
   next
   (a)
   In general
   This part shall apply to—
   (1)
   any organization exempt from tax under section 521 (relating to exemption of farmers’ cooperatives from tax), and
   (2)
   any corporation operating on a cooperative basis other than an organization—
   (A)
   which is exempt from tax under this chapter,
   (B)
   which is subject to the provisions of—
   (i)
   part II of subchapter H (relating to mutual savings banks, etc.), or
   (ii)
   subchapter L (relating to insurance companies), or
   (C)
   which is engaged in furnishing electric energy, or providing telephone service, to persons in rural areas.
   (b)
   Tax on certain farmers’ cooperatives
   An organization described in subsection (a)(1) shall be subject to the tax imposed by section 11.
   (c)
   Cross reference
   For treatment of income from load loss transactions of organizations described in subsection (a)(2)(C), see section 501(c)(12)(H).
   (Added
   Pub. L. 87–834, § 17(a)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 1045
   ; amended
   Pub. L. 108–357, title III, § 319(d)
   ,
   Oct. 22, 2004
   ,
   118 Stat. 1472
   ;
   Pub. L. 115–97, title I, § 13001(b)(2)(O)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2097
   .)
   Editorial Notes
   Amendments
   2017—Subsec. (b).
   Pub. L. 115–97
   substituted “tax imposed by section 11” for “taxes imposed by section 11 or 1201”.
   2004—Subsec. (c).
   Pub. L. 108–357
   added subsec. (c).
   Statutory Notes and Related Subsidiaries
   Effective Date of 2017 Amendment
   Amendment by
   Pub. L. 115–97
   applicable to taxable years beginning after
   Dec. 31, 2017
   , see
   section 13001(c)(1) of Pub. L. 115–97
   , set out as a note under
   section 11 of this title
   .
   Effective Date of 2004 Amendment
   Amendment by
   Pub. L. 108–357
   applicable to taxable years beginning after
   Oct. 22, 2004
   , see
   section 319(e) of Pub. L. 108–357
   , set out as a note under
   section 501 of this title
   .
   Effective Date
   Pub. L. 87–834, § 17(c)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 1051
   , as amended by
   Pub. L. 99–514, § 2
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2095
   , provided that:
   “(1)
   For the cooperatives.—
   Except as provided in paragraph (3), the amendments made by subsections (a) and (b) [enacting this subchapter, amending sections
   521
   and
   6072
   of this title, and repealing
   section 522 of this title
   ] shall apply to taxable years of organizations described in section 1381(a) of the
   Internal Revenue Code of 1986
   [formerly I.R.C. 1954] (as added by subsection (a)) beginning after
   December 31, 1962
   .
   “(2)
   For the patrons.—
   Except as provided in paragraph (3), section 1385 of the
   Internal Revenue Code of 1986
   (as added by subsection (a)) shall apply with respect to any amount received from any organization described in section 1381(a) of such Code, to the extent that such amount is paid by such organization in a taxable year of such organization beginning after
   December 31, 1962
   .
   “(3)
   Application of existing law.—
   In the case of any money,
   written notice of allocation
   , or other property paid by any organization described in
   section 1381(a)
   —
   “(A)
   before the first day of the first taxable year of such organization beginning after
   December 31, 1962
   , or
   “(B)
   on or after such first day with respect to patronage occurring before such first day,
   the tax treatment of such money,
   written notice of allocation
   , or other property (including the tax treatment of gain or loss on the redemption, sale, or other
   disposition
   of such
   written notice of allocation
   ) by any person shall be made under the
   Internal Revenue Code of 1986
   without regard to subchapter T of chapter 1 of such Code [this subchapter].”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/