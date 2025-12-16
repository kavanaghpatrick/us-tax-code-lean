/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 106ba75f-37bc-47b0-b1be-48a12c733370
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
# IRC Section 80 - Restoration of value of certain securities

This file formalizes IRC §80 (Restoration of value of certain securities).

## References
- [26 USC §80](https://www.law.cornell.edu/uscode/text/26/80)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 80 - Restoration of value of certain securities
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   In the case of a domestic corporation subject to the tax imposed by
   section 11
   or 801, if the value of any security (as defined in section 165(g)(2))—
   (1)
   which became worthless by reason of the expropriation, intervention, seizure, or similar taking by the government of any foreign country, any political subdivision thereof, or any agency or instrumentality of the foregoing of property to which such security was related, and
   (2)
   which was taken into account as a loss from the sale or exchange of a capital asset or with respect to which a deduction for a loss was allowed under section 165,
   is restored in whole or in part during any taxable year by reason of any recovery of money or other property in respect of the property to which such security was related, the value so restored (to the extent that, when added to the value so restored during prior taxable years, it does not exceed the amount of the loss described in paragraph (2)) shall, except as provided in subsection (b), be included in gross income for the taxable year in which such restoration occurs.
   (b)
   Reduction for failure to receive tax benefit
   The amount otherwise includible in gross income under subsection (a) in respect of any security shall be reduced by an amount equal to the amount (if any) of the loss described in subsection (a)(2) which did not result in a reduction of the taxpayer’s tax under this subtitle for any taxable year, determined under regulations prescribed by the Secretary.
   (c)
   Character of income
   For purposes of this subtitle—
   (1)
   Except as provided in paragraph (2), the amount included in gross income under this section shall be treated as ordinary income.
   (2)
   If the loss described in subsection (a)(2) was taken into account as a loss from the sale or exchange of a capital asset, the amount included in gross income under this section shall be treated as long-term capital gain.
   (d)
   Treatment under foreign expropriation loss recovery provisions
   This section shall not apply to any recovery of a foreign expropriation loss to which
   section 1351
   applies.
   (Added
   Pub. L. 89–384, § 1(b)(1)
   ,
   Apr. 8, 1966
   ,
   80 Stat. 101
   ; amended
   Pub. L. 94–455, title XIX
   , §§ 1901(b)(3)(K), 1906(b)(13)(A),
   Oct. 4, 1976
   ,
   90 Stat. 1793
   , 1834;
   Pub. L. 98–369, div. A, title II, § 211(b)(2)
   ,
   July 18, 1984
   ,
   98 Stat. 754
   .)
   Editorial Notes
   Amendments
   1984—Subsec. (a).
   Pub. L. 98–369
   substituted “801” for “802”.
   1976—Subsec. (b).
   Pub. L. 94–455, § 1906(b)(13)(A)
   , struck out “or his delegate” after “Secretary”.
   Subsec. (c)(1).
   Pub. L. 94–455, § 1901(b)(3)(K)
   , substituted “ordinary income” for “gain from the sale or exchange of property which is neither a capital asset nor property described in section 1231”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1984 Amendment
   Amendment by
   Pub. L. 98–369
   applicable to taxable years beginning after
   Dec. 31, 1983
   , see
   section 215 of Pub. L. 98–369
   , set out as an Effective Date note under
   section 801 of this title
   .
   Effective Date of 1976 Amendment
   Amendment by
   section 1901(b)(3)(K) of Pub. L. 94–455
   applicable with respect to taxable years beginning after
   Dec. 31, 1976
   , see
   section 1901(d) of Pub. L. 94–455
   , set out as a note under
   section 2 of this title
   .
   Effective Date
   Pub. L. 89–384, § 1(b)(3)
   ,
   Apr. 8, 1966
   ,
   80 Stat. 102
   , as amended by
   Pub. L. 99–514, § 2
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2095
   , provided that:
   “The amendments made by this subsection [enacting this section] shall apply to taxable years beginning after
   December 31, 1965
   , but only with respect to losses described in section 80(a)(2) of the
   Internal Revenue Code of 1986
   [formerly I.R.C. 1954] (as added by paragraph (1) of this subsection) which were sustained after
   December 31, 1958
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/