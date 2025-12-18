/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 17cc577a-4e40-41b2-9891-ec89a996d8af
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
# IRC Section 1472 - Withholdable payments to other foreign entities

This file formalizes IRC §1472 (Withholdable payments to other foreign entities).

## References
- [26 USC §1472](https://www.law.cornell.edu/uscode/text/26/1472)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1472 - Withholdable payments to other foreign entities
   U.S. Code
   Authorities (CFR)
   prev
   |
   next
   (a)
   In general
   In the case of any
   withholdable payment
   to a
   non-financial foreign entity
   , if—
   (1)
   the beneficial owner of such payment is such entity or any other
   non-financial foreign entity
   , and
   (2)
   the requirements of subsection (b) are not met with respect to such beneficial owner,
   then the
   withholding agent
   with respect to such payment shall deduct and withhold from such payment a tax equal to 30 percent of the amount of such payment.
   (b)
   Requirements for waiver of withholding
   The requirements of this subsection are met with respect to the beneficial owner of a payment if—
   (1)
   such beneficial owner or the payee provides the
   withholding agent
   with either—
   (A)
   a certification that such beneficial owner does not have any
   substantial United States owners
   , or
   (B)
   the name, address, and TIN of each
   substantial United States owner
   of such beneficial owner,
   (2)
   the
   withholding agent
   does not know, or have reason to know, that any information provided under paragraph (1) is incorrect, and
   (3)
   the
   withholding agent
   reports the information provided under paragraph (1)(B) to the Secretary in such manner as the Secretary may provide.
   (c)
   Exceptions
   Subsection (a) shall not apply to—
   (1)
   except as otherwise provided by the Secretary, any payment beneficially owned by—
   (A)
   any corporation the stock of which is regularly traded on an established securities market,
   (B)
   any corporation which is a member of the same expanded affiliated group (as defined in
   section 1471(e)(2)
   without regard to the last sentence thereof) as a corporation described in subparagraph (A),
   (C)
   any entity which is organized under the laws of a possession of the United States and which is wholly owned by one or more bona fide residents (as defined in section 937(a)) of such possession,
   (D)
   any foreign government, any political subdivision of a foreign government, or any wholly owned agency or instrumentality of any one or more of the foregoing,
   (E)
   any international organization or any wholly owned agency or instrumentality thereof,
   (F)
   any foreign central bank of issue, or
   (G)
   any other class of persons identified by the Secretary for purposes of this subsection, and
   (2)
   any class of payments identified by the Secretary for purposes of this subsection as posing a low risk of tax evasion.
   (d)
   Non-financial foreign entity
   For purposes of this section, the term “
   non-financial foreign entity
   ” means any
   foreign entity
   which is not a financial institution (as defined in
   section 1471(d)(5)
   ).
   (Added
   Pub. L. 111–147, title V, § 501(a)
   ,
   Mar. 18, 2010
   ,
   124 Stat. 102
   .)
   CFR Title
   Parts
   26
   1
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/