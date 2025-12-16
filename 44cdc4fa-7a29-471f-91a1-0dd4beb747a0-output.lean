/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 44cdc4fa-7a29-471f-91a1-0dd4beb747a0
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

-- Common definitions for US Tax Code formalization
def Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

inductive FilingStatus
  | Single                         -- IRC §1(c)
  | MarriedFilingJointly          -- IRC §1(a)
  | MarriedFilingSeparately       -- IRC §1(d)
  | HeadOfHousehold               -- IRC §1(b)
  | QualifyingWidower             -- IRC §2(b)
  | Estate                         -- IRC §1(e)(1)
  | Trust                          -- IRC §1(e)(2)
  deriving Repr, DecidableEq, Inhabited

structure Taxpayer where
  id : String
  filingStatus : FilingStatus
  taxYear : TaxYear

/-!
# IRC Section 87 - Alcohol and biodiesel fuels credits

This file formalizes IRC §87 (Alcohol and biodiesel fuels credits).

## References
- [26 USC §87](https://www.law.cornell.edu/uscode/text/26/87)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 87 - Alcohol and biodiesel fuels credits
   U.S. Code
   Notes
   prev
   |
   next
   Gross income includes—
   (1)
   the amount of the alcohol fuel credit determined with respect to the taxpayer for the taxable year under section 40(a),
   (2)
   the biodiesel fuels credit determined with respect to the taxpayer for the taxable year under section 40A(a), and
   (3)
   the sustainable aviation fuel credit determined with respect to the taxpayer for the taxable year under section 40B(a).
   (Added
   Pub. L. 96–223, title II, § 232(c)(1)
   ,
   Apr. 2, 1980
   ,
   94 Stat. 276
   , § 86; renumbered § 87,
   Pub. L. 98–21, title I, § 121(a)
   ,
   Apr. 20, 1983
   ,
   97 Stat. 80
   ; amended
   Pub. L. 98–369, div. A, title IV, § 474(r)(3)
   ,
   July 18, 1984
   ,
   98 Stat. 839
   ;
   Pub. L. 108–357, title III, § 302(c)(1)(A)
   ,
   Oct. 22, 2004
   ,
   118 Stat. 1465
   ;
   Pub. L. 117–169, title I, § 13203(e)
   ,
   Aug. 16, 2022
   ,
   136 Stat. 1935
   .)
   Editorial Notes
   Amendments
   2022—Par. (3).
   Pub. L. 117–169
   added par. (3).
   2004—
   Pub. L. 108–357
   amended section catchline and text generally. Prior to amendment, text read as follows: “Gross income includes the amount of the alcohol fuel credit determined with respect to the taxpayer for the taxable year under section 40(a).”
   1984—
   Pub. L. 98–369
   amended section generally, substituting “the amount of the alcohol fuel credit determined with respect to the taxpayer for the taxable year under section 40(a)” for “an amount equal to the amount of the credit allowable to the taxpayer under section 44E for the taxable year (determined without regard to subsection (e) thereof)”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 2022 Amendment
   Amendment by
   Pub. L. 117–169
   applicable to fuel sold or used after
   Dec. 31, 2022
   , see
   section 13203(f) of Pub. L. 117–169
   , set out as an Effective Date note under
   section 40B of this title
   .
   Effective Date of 2004 Amendment
   Amendment by
   Pub. L. 108–357
   applicable to fuel produced, and sold or used, after
   Dec. 31, 2004
   , in taxable years ending after such date, see
   section 302(d) of Pub. L. 108–357
   , set out as a note under
   section 38 of this title
   .
   Effective Date of 1984 Amendment
   Amendment by
   Pub. L. 98–369
   applicable to taxable years beginning after
   Dec. 31, 1983
   , and to carrybacks from such years, see
   section 475(a) of Pub. L. 98–369
   , set out as a note under
   section 21 of this title
   .
   Effective Date
   Section applicable to sales or uses after
   Sept. 30, 1980
   , in taxable years ending after such date, see
   section 232(h)(1) of Pub. L. 96–223
   , set out as a note under
   section 40 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/