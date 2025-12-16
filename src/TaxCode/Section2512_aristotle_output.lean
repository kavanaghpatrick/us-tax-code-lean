/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8a5bbf21-cb80-4b45-9de7-cbe69a08aaf0
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
# IRC Section 2512 - Valuation of gifts

This file formalizes IRC §2512 (Valuation of gifts).

## References
- [26 USC §2512](https://www.law.cornell.edu/uscode/text/26/2512)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2512 - Valuation of gifts
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   If the gift is made in property, the value thereof at the date of the gift shall be considered the amount of the gift.
   (b)
   Where property is transferred for less than an adequate and full consideration in money or money’s worth, then the amount by which the value of the property exceeded the value of the consideration shall be deemed a gift, and shall be included in computing the amount of gifts made during the calendar year.
   (c)
   Cross reference
   For individual’s right to be furnished on request a statement regarding any valuation made by the Secretary of a gift by that individual, see section 7517.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 406
   ;
   Pub. L. 91–614, title I, § 102(b)(1)
   ,
   Dec. 31, 1970
   ,
   84 Stat. 1840
   ;
   Pub. L. 94–455, title XX, § 2008(a)(2)(B)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1891
   ;
   Pub. L. 97–34, title IV, § 442(b)(1)
   ,
   Aug. 13, 1981
   ,
   95 Stat. 322
   .)
   Editorial Notes
   Amendments
   1981—Subsec. (b).
   Pub. L. 97–34
   substituted “calendar year” for “calendar quarters”.
   1976—Subsec. (c).
   Pub. L. 94–455
   added subsec. (c).
   1970—Subsec. (b).
   Pub. L. 91–614
   substituted “calendar quarter” for “calendar year”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1981 Amendment
   Amendment by
   Pub. L. 97–34
   applicable with respect to gifts made after
   Dec. 31, 1981
   , see
   section 442(e) of Pub. L. 97–34
   , set out as a note under
   section 2501 of this title
   .
   Effective Date of 1970 Amendment
   Amendment by
   Pub. L. 91–614
   applicable with respect to gifts made after
   Dec. 31, 1970
   , see
   section 102(e) of Pub. L. 91–614
   , set out as a note under
   section 2501 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/