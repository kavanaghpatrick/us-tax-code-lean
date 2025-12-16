/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9578dc8a-4897-4af3-b10d-5ed98e9dea62

Aristotle encountered an error processing this file. The team has been notified.

-/


import Mathlib

def Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq

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
# IRC Section 594 - Alternative tax for mutual savings banks conducting life insurance business

This file formalizes IRC §594 (Alternative tax for mutual savings banks conducting life insurance business).

## References
- [26 USC §594](https://www.law.cornell.edu/uscode/text/26/594)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 594 - Alternative tax for mutual savings banks conducting life insurance business
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Alternative tax
   In the case of a
   mutual savings bank
   not having capital stock represented by shares, authorized under State law to engage in the business of issuing life insurance contracts, and which conducts a life insurance business in a separate department the accounts of which are maintained separately from the other accounts of the
   mutual savings bank
   , there shall be imposed in lieu of the tax imposed by section 11, a tax consisting of the sum of the partial taxes determined under paragraphs (1) and (2):
   (1)
   A partial tax computed on the taxable income determined without regard to any items of gross income or deductions properly allocable to the business of the life insurance department, at the rates and in the manner as if this section had not been enacted; and
   (2)
   a partial tax computed on the income of the life insurance department determined without regard to any items of gross income or deductions not properly allocable to such department, at the rates and in the manner provided in subchapter L (sec. 801 and following) with respect to life insurance companies.
   (b)
   Limitations of section
   Subsection (a) shall apply only if the life insurance department would, if it were treated as a separate corporation, qualify as a life insurance company under section 816.

-- TODO: Add type definitions
-- TODO: Add main functions
-- TODO: Add theorems to prove