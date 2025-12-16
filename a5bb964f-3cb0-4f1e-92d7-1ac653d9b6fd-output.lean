/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a5bb964f-3cb0-4f1e-92d7-1ac653d9b6fd
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
# IRC Section 1473 - Definitions

This file formalizes IRC §1473 (Definitions).

## References
- [26 USC §1473](https://www.law.cornell.edu/uscode/text/26/1473)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1473 - Definitions
   U.S. Code
   Authorities (CFR)
   prev
   |
   next
   For purposes of this chapter—
   (1)
   Withholdable payment
   Except as otherwise provided by the Secretary—
   (A)
   In general
   The term “
   withholdable payment
   ” means—
   (i)
   any payment of interest (including any original issue discount), dividends, rents, salaries, wages, premiums, annuities, compensations, remunerations, emoluments, and other fixed or determinable annual or periodical gains, profits, and income, if such payment is from sources within the United States, and
   (ii)
   any gross proceeds from the sale or other disposition of any property of a type which can produce interest or dividends from sources within the United States.
   (B)
   Exception for income connected with United States business
   Such term shall not include any item of income which is taken into account under section
   871(b)(1)
   or
   882(a)(1)
   for the taxable year.
   (C)
   Special rule for sourcing interest paid by foreign branches of domestic financial institutions
   Subparagraph (B) of
   section 861(a)(1)
   shall not apply.
   (2)
   Substantial United States owner
   (A)
   In general
   The term “
   substantial United States owner
   ” means—
   (i)
   with respect to any corporation, any
   specified United States person
   which owns, directly or indirectly, more than 10 percent of the stock of such corporation (by vote or value),
   (ii)
   with respect to any partnership, any
   specified United States person
   which owns, directly or indirectly, more than 10 percent of the profits interests or capital interests in such partnership, and
   (iii)
   in the case of a trust—
   (I)
   any
   specified United States person
   treated as an owner of any portion of such trust under subpart E of part I of subchapter J of chapter 1, and
   (II)
   to the extent provided by the Secretary in regulations or other guidance, any
   specified United States person
   which holds, directly or indirectly, more than 10 percent of the beneficial interests of such trust.
   (B)
   Special rule for investment vehicles
   In the case of any financial institution described in section 1471(d)(5)(C), clauses (i), (ii), and (iii) of subparagraph (A) shall be applied by substituting “0 percent” for “10 percent”.
   (3)
   Specified United States person
   Except as otherwise provided by the Secretary, the term “
   specified United States person
   ” means any United States person other than—
   (A)
   any corporation the stock of which is regularly traded on an established securities market,
   (B)
   any corporation which is a member of the same expanded affiliated group (as defined in
   section 1471(e)(2)
   without regard to the last sentence thereof) as a corporation the stock of which is regularly traded on an established securities market,
   (C)
   any organization exempt from taxation under
   section 501(a)
   or an individual retirement plan,
   (D)
   the United States or any wholly owned agency or instrumentality thereof,
   (E)
   any State, the District of Columbia, any possession of the United States, any political subdivision of any of the foregoing, or any wholly owned agency or instrumentality of any one or more of the foregoing,
   (F)
   any bank (as defined in
   section 581
   ),
   (G)
   any real estate investment trust (as defined in
   section 856
   ),
   (H)
   any regulated investment company (as defined in
   section 851
   ),
   (I)
   any common trust fund (as defined in
   section 584(a)
   ), and
   (J)
   any trust which—
   (i)
   is exempt from tax under section 664(c), or
   (ii)
   is described in section 4947(a)(1).
   (4)
   Withholding agent
   The term “
   withholding agent
   ” means all persons, in whatever capacity acting, having the control, receipt, custody, disposal, or payment of any
   withholdable payment
   .
   (5)
   Foreign entity
   The term “
   foreign entity
   ” means any entity which is not a United States person.
   (Added
   Pub. L. 111–147, title V, § 501(a)
   ,
   Mar. 18, 2010
   ,
   124 Stat. 103
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