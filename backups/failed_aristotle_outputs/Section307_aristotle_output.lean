/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 866224bc-c29a-4b30-8ff0-2a205f746a0d
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
# IRC Section 307 - Basis of stock and stock rights acquired in distributions

This file formalizes IRC §307 (Basis of stock and stock rights acquired in distributions).

## References
- [26 USC §307](https://www.law.cornell.edu/uscode/text/26/307)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 307 - Basis of stock and stock rights acquired in distributions
   U.S. Code
   Notes
   prev
   | next
   (a)
   General rule
   If a
   shareholder
   in a corporation receives its stock or rights to acquire its stock (referred to in this subsection as “new stock”) in a distribution to which section 305(a) applies, then the basis of such new stock and of the stock with respect to which it is distributed (referred to in this section as “old stock”), respectively, shall, in the
   shareholder
   ’s hands, be determined by allocating between the old stock and the new stock the adjusted basis of the old stock. Such allocation shall be made under regulations prescribed by the Secretary.
   (b)
   Exception for certain stock rights
   (1)
   In general
   If—
   (A)
   a corporation distributes rights to acquire its stock to a
   shareholder
   in a distribution to which
   section 305(a)
   applies, and
   (B)
   the fair market value of such rights at the time of the distribution is less than 15 percent of the fair market value of the old stock at such time,
   then subsection (a) shall not apply and the basis of such rights shall be zero, unless the taxpayer elects under paragraph (2) of this subsection to determine the basis of the old stock and of the stock rights under the method of allocation provided in subsection (a).
   (2)
   Election
   The election referred to in paragraph (1) shall be made in the return filed within the time prescribed by law (including extensions thereof) for the taxable year in which such rights were received. Such election shall be made in such manner as the Secretary may by regulations prescribe, and shall be irrevocable when made.
   (c)
   Cross reference
   For basis of stock and stock rights distributed before
   June 22, 1954
   , see section 1052.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 93
   ;
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1834
   .)
   Editorial Notes
   Amendments
   1976—Subsecs. (a), (b)(2).
   Pub. L. 94–455
   struck out “or his delegate” after “Secretary”.
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/