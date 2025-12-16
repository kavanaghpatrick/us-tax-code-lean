/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6813c44c-5b62-4187-b8c4-34bf23a691f4
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
# IRC Section 1288 - Treatment of original issue discount on tax-exempt obligations

This file formalizes IRC §1288 (Treatment of original issue discount on tax-exempt obligations).

## References
- [26 USC §1288](https://www.law.cornell.edu/uscode/text/26/1288)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1288 - Treatment of original issue discount on tax-exempt obligations
   U.S. Code
   Notes
   prev
   | next
   (a)
   General rule
   Original issue discount on any
   tax-exempt obligation
   shall be treated as accruing—
   (1)
   for purposes of section 163, in the manner provided by
   section 1272(a)
   (determined without regard to paragraph (7) thereof), and
   (2)
   for purposes of determining the adjusted basis of the holder, in the manner provided by
   section 1272(a)
   (determined with regard to paragraph (7) thereof).
   (b)
   Definitions and special rules
   For purposes of this section—
   (1)
   Original issue discount
   The term “
   original issue discount
   ” has the meaning given to such term by
   section 1273(a)
   without regard to paragraph (3) thereof. In applying section 483 or 1274, under regulations prescribed by the Secretary, appropriate adjustments shall be made to the applicable Federal rate to take into account the tax exemption for interest on the obligation.
   (2)
   Tax-exempt obligation
   The term “
   tax-exempt obligation
   ” has the meaning given to such term by section 1275(a)(3).
   (3)
   Short-term obligations
   In applying this section to obligations with maturity of 1 year or less, rules similar to the rules of
   section 1283(b)
   shall apply.
   (Added
   Pub. L. 98–369, div. A, title I, § 41(a)
   ,
   July 18, 1984
   ,
   98 Stat. 553
   ; amended
   Pub. L. 100–647, title I, § 1006(u)(3)
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3427
   .)
   Editorial Notes
   Amendments
   1988—Subsec. (a).
   Pub. L. 100–647
   substituted “paragraph (7)” for “paragraph (6)” in pars. (1) and (2).
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
   Section applicable to taxable years ending after
   July 18, 1984
   , and applicable to obligations issued after
   Sept. 3, 1982
   , and acquired after
   Mar. 1, 1984
   , see
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