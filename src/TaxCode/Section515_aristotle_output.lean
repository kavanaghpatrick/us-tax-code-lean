/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8b34e963-6689-40a7-9138-ea7457c2ddca
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
# IRC Section 515 - Taxes of foreign countries and possessions of the United States

This file formalizes IRC §515 (Taxes of foreign countries and possessions of the United States).

## References
- [26 USC §515](https://www.law.cornell.edu/uscode/text/26/515)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 515 - Taxes of foreign countries and possessions of the United States
   U.S. Code
   prev
   | next
   The amount of taxes imposed by foreign countries and possessions of the United States shall be allowed as a credit against the tax of an organization subject to the tax imposed by section 511 to the extent provided in section 901; and in the case of the tax imposed by section 511, the term “taxable income” as used in section 901 shall be read as “
   unrelated business taxable income
   ”.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 176
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/

-- TODO: Add type definitions

-- TODO: Add main functions

-- TODO: Add theorems to prove

-- Example usage
#eval "Section loaded"