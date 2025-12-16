/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d5da5fcf-d0fe-4527-b6ac-af6d879b2108
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
# IRC Section 2044 - Certain property for which marital deduction was previously allowed

This file formalizes IRC §2044 (Certain property for which marital deduction was previously allowed).

## References
- [26 USC §2044](https://www.law.cornell.edu/uscode/text/26/2044)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2044 - Certain property for which marital deduction was previously allowed
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   The value of the gross estate shall include the value of any property to which this section applies in which the decedent had a qualifying income interest for life.
   (b)
   Property to which this section applies
   This section applies to any property if—
   (1)
   a deduction was allowed with respect to the transfer of such property to the decedent—
   (A)
   under
   section 2056
   by reason of subsection (b)(7) thereof, or
   (B)
   under
   section 2523
   by reason of subsection (f) thereof, and
   (2)
   section 2519 (relating to dispositions of certain life estates) did not apply with respect to a disposition by the decedent of part or all of such property.
   (c)
   Property treated as having passed from decedent
   For purposes of this chapter and chapter 13, property includible in the gross estate of the decedent under subsection (a) shall be treated as property passing from the decedent.
   (Added
   Pub. L. 97–34, title IV, § 403(d)(3)(A)(i)
   ,
   Aug. 13, 1981
   ,
   95 Stat. 304
   ; amended
   Pub. L. 97–448, title I, § 104(a)(1)(B)
   ,
   Jan. 12, 1983
   ,
   96 Stat. 2380
   .)
   Editorial Notes
   Prior Provisions
   A prior
   section 2044
   was renumbered
   section 2045 of this title
   .
   Amendments
   1983—Subsec. (c).
   Pub. L. 97–448
   added subsec. (c).
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
   Section applicable to estates of decedents dying after
   Dec. 31, 1981
   , see
   section 403(e) of Pub. L. 97–34
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