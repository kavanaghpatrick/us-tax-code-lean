/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 595d1fec-48b4-479b-94d0-08d52cbe030f
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5a3af837-1548-4c66-bfda-4dac6d78939e
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
# IRC Section 73 - Services of child

This file formalizes IRC §73 (Services of child).

## References
- [26 USC §73](https://www.law.cornell.edu/uscode/text/26/73)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 73 - Services of child
   U.S. Code
   prev
   |
   next
   (a)
   Treatment of amounts received
   Amounts received in respect of the services of a child shall be included in his gross income and not in the gross income of the
   parent
   , even though such amounts are not received by the child.
   (b)
   Treatment of expenditures
   All expenditures by the
   parent
   or the child attributable to amounts which are includible in the gross income of the child (and not of the
   parent
   ) solely by reason of subsection (a) shall be treated as paid or incurred by the child.
   (c)
   Parent defined
   For purposes of this section, the term “
   parent
   ” includes an individual who is entitled to the services of a child by reason of having parental rights and duties in respect of the child.
   (d)
   Cross reference
   For assessment of tax against
   parent
   in certain cases, see section 6201(c).
   (Aug. 16, 1954, ch. 736,
   68A Stat. 24
   .)
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/