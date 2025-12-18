/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7f6a31fa-717e-4920-a228-5f2475d23564
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
# IRC Section 1287 - Denial of capital gain treatment for gains on certain obligations not in registered form

This file formalizes IRC §1287 (Denial of capital gain treatment for gains on certain obligations not in registered form).

## References
- [26 USC §1287](https://www.law.cornell.edu/uscode/text/26/1287)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1287 - Denial of capital gain treatment for gains on certain obligations not in registered form
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   In general
   If any
   registration-required obligation
   is not in
   registered form
   , any gain on the sale or other
   disposition
   of such obligation shall be treated as ordinary income (unless the issuance of such obligation was subject to tax under
   section 4701
   ).
   (b)
   Definitions
   For purposes of subsection (a)—
   (1)
   Registration-required obligation
   The term “
   registration-required obligation
   ” has the meaning given to such term by section 163(f)(2).
   (2)
   Registered form
   The term “
   registered form
   ” has the same meaning as when used in section 163(f).
   (Added
   Pub. L. 98–369, div. A, title I, § 41(a)
   ,
   July 18, 1984
   ,
   98 Stat. 552
   ; amended
   Pub. L. 111–147, title V, § 502(a)(2)(D)
   ,
   Mar. 18, 2010
   ,
   124 Stat. 107
   .)
   Editorial Notes
   Amendments
   2010—Subsec. (b)(1).
   Pub. L. 111–147
   struck out “except that clause (iv) of subparagraph (A), and subparagraph (B), of such section shall not apply” before period.
   Statutory Notes and Related Subsidiaries
   Effective Date of 2010 Amendment
   Amendment by
   Pub. L. 111–147
   applicable to obligations issued after the date which is 2 years after
   Mar. 18, 2010
   , see
   section 502(f) of Pub. L. 111–147
   , set out as a note under
   section 149 of this title
   .
   Effective Date
   Section applicable to taxable years ending after
   July 18, 1984
   , except as otherwise provided, see
   section 44 of Pub. L. 98–369
   , set out as a note under
   section 1271 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/