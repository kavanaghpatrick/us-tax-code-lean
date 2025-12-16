/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c3706f3e-16ad-4932-a0d5-aeb6e261f77f
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
# IRC Section 843 - Annual accounting period

This file formalizes IRC §843 (Annual accounting period).

## References
- [26 USC §843](https://www.law.cornell.edu/uscode/text/26/843)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 843 - Annual accounting period
   U.S. Code
   Notes
   prev
   |
   next
   For purposes of this subtitle, the annual accounting period for each insurance company subject to a tax imposed by this subchapter shall be the calendar year. Under regulations prescribed by the Secretary, an insurance company which joins in the filing of a consolidated return (or is required to so file) may adopt the taxable year of the common parent corporation even though such year is not a calendar year.
   (Added Mar. 13, 1956, ch. 83, § 4(a),
   70 Stat. 48
   ; amended
   Pub. L. 94–455, title XV, § 1507(b)(2)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1740
   .)
   Editorial Notes
   Amendments
   1976—
   Pub. L. 94–455
   inserted provision permitting an insurance company which joins in the filing of a consolidated return to adopt the taxable year of the common parent corporation even though such year is not a calendar year.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1976 Amendment
   Amendment by
   Pub. L. 94–455
   applicable to taxable years beginning after
   Dec. 31, 1980
   , see
   section 1507(c)(1) of Pub. L. 94–455
   , set out as a note under
   section 1504 of this title
   .
   Effective Date
   Section applicable only to taxable years beginning after
   Dec. 31, 1954
   , see Effective Date of 1956 Amendment note set out under
   section 316 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/