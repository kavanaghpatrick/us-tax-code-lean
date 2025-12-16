/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 104a5f59-5c07-40fc-9c7a-a122627140cc
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
# IRC Section 177 - Repealed. Pub. L. 99–514, title II, § 241(a), Oct. 22, 1986, 100 Stat. 2181]

This file formalizes IRC §177 (Repealed. Pub. L. 99–514, title II, § 241(a), Oct. 22, 1986, 100 Stat. 2181]).

## References
- [26 USC §177](https://www.law.cornell.edu/uscode/text/26/177)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 177 - Repealed. Pub. L. 99–514, title II, § 241(a), Oct. 22, 1986, 100 Stat. 2181]
   U.S. Code
   Notes
   prev
   |
   next
   Section, added June 29, 1956, ch. 464, § 4(a),
   70 Stat. 406
   ; amended
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   90 Stat. 1834
   , related to deductions for trademark and trade name expenditures.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Pub. L. 99–514, title II, § 241(c)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2181
   , provided that:
   “(1)
   In general.—
   Except as provided in paragraph (2), the amendments made by this section [amending sections
   312
   and
   1016
   of this title and repealing this section] shall apply to expenditures paid or incurred after
   December 31, 1986
   .
   “(2)
   Transitional rule.—
   The amendments made by this section shall not apply to any expenditure incurred—
   “(A)
   pursuant to a binding contract entered into before
   March 2, 1986
   , or
   “(B)
   with respect to the development, protection, expansion, registration, or defense of a trademark or trade name commenced before
   March 2, 1986
   , but only if not less than the lesser of $1,000,000 or 5 percent of the aggregate cost of such development, protection, expansion, registration, or defense has been incurred or committed before such date.
   The preceding sentence shall not apply to any expenditure with respect to a trademark or trade name placed in service after
   December 31, 1987
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/