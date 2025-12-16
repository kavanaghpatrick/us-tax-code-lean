/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6c88efb6-65d0-428f-bd2f-bb40e83c32ca
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
# IRC Section 2519 - Dispositions of certain life estates

This file formalizes IRC §2519 (Dispositions of certain life estates).

## References
- [26 USC §2519](https://www.law.cornell.edu/uscode/text/26/2519)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2519 - Dispositions of certain life estates
   U.S. Code
   Notes
   prev
   | next
   (a)
   General rule
   For purposes of this chapter and chapter 11, any disposition of all or part of a qualifying income interest for life in any property to which this section applies shall be treated as a transfer of all interests in such property other than the qualifying income interest.
   (b)
   Property to which this subsection applies
   This section applies to any property if a deduction was allowed with respect to the transfer of such property to the donor—
   (1)
   under
   section 2056
   by reason of subsection (b)(7) thereof, or
   (2)
   under
   section 2523
   by reason of subsection (f) thereof.
   (c)
   Cross reference
   For right of recovery for gift tax in the case of property treated as transferred under this section, see section 2207A(b).
   (Added
   Pub. L. 97–34, title IV, § 403(d)(3)(B)(i)
   ,
   Aug. 13, 1981
   ,
   95 Stat. 304
   ; amended
   Pub. L. 97–448, title I, § 104(a)(3)
   , (7),
   Jan. 12, 1983
   ,
   96 Stat. 2380
   , 2381.)
   Editorial Notes
   Amendments
   1983—
   Pub. L. 97–448, § 104(a)(3)(B)
   , amended directory language of
   Pub. L. 97–34, § 403(d)(3)(B)(i)
   , to clarify that this section be inserted at end of subchapter B of chapter 12, rather than at end of subchapter B of chapter 11, and did not involve any change in text.
   Subsec. (a).
   Pub. L. 97–448, § 104(a)(3)(A)
   , substituted “For purposes of this chapter and chapter 11, any disposition” for “Any disposition” and “treated as a transfer of all interests in such property other than the qualifying income interest” for “treated as a transfer of such property”.
   Subsec. (c).
   Pub. L. 97–448, § 104(a)(7)
   , added subsec. (c).
   Statutory Notes and Related Subsidiaries
   Effective Date of 1983 Amendment
   Amendment by
   Pub. L. 97–448
   effective, except as otherwise provided, as if it had been included in the provision of the
   Economic Recovery Tax Act of 1981
   ,
   Pub. L. 97–34
   , to which such amendment relates, see
   section 109 of Pub. L. 97–448
   , set out as a note under
   section 1 of this title
   .
   Effective Date
   Section applicable to gifts made after
   Dec. 31, 1981
   , see
   section 403(e)(2) of Pub. L. 97–34
   , set out as an Effective Date of 1981 Amendment note under
   section 2056 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/