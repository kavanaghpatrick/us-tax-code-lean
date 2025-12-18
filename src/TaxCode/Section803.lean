/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 95d102b0-1d53-4623-a1bf-b9e0570d5b64
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
# IRC Section 803 - Life insurance gross income

This file formalizes IRC §803 (Life insurance gross income).

## References
- [26 USC §803](https://www.law.cornell.edu/uscode/text/26/803)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 803 - Life insurance gross income
   U.S. Code
   Notes
   (a)
   In general
   For purposes of this part, the term “
   life insurance gross income
   ” means the sum of the following amounts:
   (1)
   Premiums
   (A)
   The
   gross amount of premiums and other consideration
   on insurance and
   annuity contracts,
   less
   (B)
   return premiums, and premiums and other consideration arising out of indemnity reinsurance.
   (2)
   Decreases in certain reserves
   Each net decrease in reserves which is required by
   section 807(a)
   to be taken into account under this paragraph.
   (3)
   Other amounts
   All amounts not includible under paragraph (1) or (2) which under this subtitle are includible in gross income.
   (b)
   Special rules for premiums
   (1)
   Certain items included
   For purposes of subsection (a)(1)(A), the term “
   gross amount of premiums and other consideration
   ” includes—
   (A)
   advance premiums,
   (B)
   deposits,
   (C)
   fees,
   (D)
   assessments,
   (E)
   consideration in respect of assuming liabilities under contracts not issued by the taxpayer, and
   (F)
   the amount of
   policyholder dividends
   reimbursable to the taxpayer by a reinsurer in respect of reinsured policies,
   on insurance and
   annuity contracts
   .
   (2)
   Policyholder dividends excluded from return premiums
   For purposes of subsection (a)(1)(B)—
   (A)
   In general
   Except as provided in subparagraph (B), the term “return premiums” does not include any
   policyholder dividends
   .
   (B)
   Exception for indemnity reinsurance
   Subparagraph (A) shall not apply to amounts of premiums or other consideration returned to another life insurance company in respect of indemnity reinsurance.
   (Added
   Pub. L. 98–369, div. A, title II, § 211(a)
   ,
   July 18, 1984
   ,
   98 Stat. 721
   .)
   Editorial Notes
   Prior Provisions
   A prior section 803, acts Aug. 16, 1954, ch. 736,
   68A Stat. 256
   ; Mar. 13, 1956, ch. 83, § 2,
   70 Stat. 39
   , related to income and deductions in the case of life insurance companies, prior to the general revision of this part by
   Pub. L. 86–69, § 2(a)
   ,
   June 25, 1959
   ,
   73 Stat. 112
   .
   Statutory Notes and Related Subsidiaries
   Effective Date
   Section applicable to taxable years beginning after
   Dec. 31, 1983
   , see
   section 215 of Pub. L. 98–369
   , set out as a note under
   section 801 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/