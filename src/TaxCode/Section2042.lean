/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9110f04b-a7c6-4ab4-9f92-b942bc67d702
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
# IRC Section 2042 - Proceeds of life insurance

This file formalizes IRC §2042 (Proceeds of life insurance).

## References
- [26 USC §2042](https://www.law.cornell.edu/uscode/text/26/2042)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2042 - Proceeds of life insurance
   U.S. Code
   Notes
   prev
   |
   next
   The value of the gross estate shall include the value of all property—
   (1)
   Receivable by the executor
   To the extent of the amount receivable by the executor as insurance under policies on the life of the decedent.
   (2)
   Receivable by other beneficiaries
   To the extent of the amount receivable by all other beneficiaries as insurance under policies on the life of the decedent with respect to which the decedent possessed at his death any of the incidents of ownership, exercisable either alone or in conjunction with any other person. For purposes of the preceding sentence, the term “
   incident of ownership
   ” includes a
   reversionary interest
   (whether arising by the express terms of the policy or other instrument or by operation of law) only if the value of such
   reversionary interest
   exceeded 5 percent of the value of the policy immediately before the death of the decedent. As used in this paragraph, the term “
   reversionary interest
   ” includes a possibility that the policy, or the proceeds of the policy, may return to the decedent or his estate, or may be subject to a power of disposition by him. The value of a
   reversionary interest
   at any time shall be determined (without regard to the fact of the decedent’s death) by usual methods of valuation, including the use of tables of mortality and actuarial principles, pursuant to regulations prescribed by the Secretary. In determining the value of a possibility that the policy or proceeds thereof may be subject to a power of disposition by the decedent, such possibility shall be valued as if it were a possibility that such policy or proceeds may return to the decedent or his estate.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 387
   ;
   Pub. L. 94–455, title XIX, § 1906(b)(13)
   (A),
   Oct. 4, 1976
   ,
   90 Stat. 1834
   .)
   Editorial Notes
   Amendments
   1976—
   Pub. L. 94–455
   struck out “or his delegate” after “Secretary”.
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/