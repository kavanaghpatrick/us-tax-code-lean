/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c77e70be-206a-47ac-9fca-777803d445d9
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
# IRC Section 2045 - Prior interests

This file formalizes IRC §2045 (Prior interests).

## References
- [26 USC §2045](https://www.law.cornell.edu/uscode/text/26/2045)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2045 - Prior interests
   U.S. Code
   Notes
   prev
   |
   next
   Except as otherwise specifically provided by law,
   sections 2034
   to 2042, inclusive, shall apply to the transfers, trusts, estates, interests, rights, powers, and relinquishment of powers, as severally enumerated and described therein, whenever made, created, arising, existing, exercised, or relinquished.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 388
   , § 2044;
   Pub. L. 94–455, title XX, § 2001(c)(1)(M)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1853
   ; renumbered § 2045,
   Pub. L. 97–34, title IV, § 403(d)(3)(A)(i)
   ,
   Aug. 13, 1981
   ,
   95 Stat. 304
   .)
   Editorial Notes
   Prior Provisions
   A prior
   section 2045
   was renumbered
   section 2046 of this title
   .
   Amendments
   1976—
   Pub. L. 94–455
   substituted “specifically provided by law” for “specifically provided therein”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1976 Amendment
   Amendment by
   Pub. L. 94–455
   applicable to estates of decedents dying after
   Dec. 31, 1976
   , see
   section 2001(d) of Pub. L. 94–455
   , set out as a note under
   section 2001 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/