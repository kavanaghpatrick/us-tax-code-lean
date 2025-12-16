/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2f28efe7-0828-4f59-b0ae-05ebbff55ca0
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
# IRC Section 2663 - Regulations

This file formalizes IRC §2663 (Regulations).

## References
- [26 USC §2663](https://www.law.cornell.edu/uscode/text/26/2663)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2663 - Regulations
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   The Secretary shall prescribe such regulations as may be necessary or appropriate to carry out the purposes of this chapter, including—
   (1)
   such regulations as may be necessary to coordinate the provisions of this chapter with the recapture tax imposed under section 2032A(c),
   (2)
   regulations (consistent with the principles of chapters 11 and 12) providing for the application of this chapter in the case of transferors who are nonresidents not citizens of the United States, and
   (3)
   regulations providing for such adjustments as may be necessary to the application of this chapter in the case of any arrangement which, although not a trust, is treated as a trust under section 2652(b).
   (Added
   Pub. L. 99–514, title XIV, § 1431(a)
   ,
   Oct. 22, 1986
   ,
   100 Stat. 2729
   ; amended
   Pub. L. 100–647, title I, § 1014(g)(10)
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3565
   .)
   Editorial Notes
   Amendments
   1988—Par. (3).
   Pub. L. 100–647
   added par. (3).
   Statutory Notes and Related Subsidiaries
   Effective Date of 1988 Amendment
   Amendment by
   Pub. L. 100–647
   effective, except as otherwise provided, as if included in the provision of the
   Tax Reform Act of 1986
   ,
   Pub. L. 99–514
   , to which such amendment relates, see
   section 1019(a) of Pub. L. 100–647
   , set out as a note under
   section 1 of this title
   .
   Effective Date
   Section applicable to
   generation-skipping transfers
   (within the meaning of
   section 2611 of this title
   ) made after
   Oct. 22, 1986
   , except as otherwise provided, see
   section 1433 of Pub. L. 99–514
   , set out as a note under
   section 2601 of this title
   .
   CFR Title
   Parts
   26
   26
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/