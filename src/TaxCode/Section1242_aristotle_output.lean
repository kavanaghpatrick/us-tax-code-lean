/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0467cfd1-2c37-45b2-ba57-c7c4f524ec69
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
# IRC Section 1242 - Losses on small business investment company stock

This file formalizes IRC §1242 (Losses on small business investment company stock).

## References
- [26 USC §1242](https://www.law.cornell.edu/uscode/text/26/1242)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1242 - Losses on small business investment company stock
   U.S. Code
   Notes
   prev
   |
   next
   If—
   (1)
   a loss is on
   stock
   in a small business investment company operating under the
   Small Business Investment Act of 1958
   , and
   (2)
   such loss would (but for this section) be a loss from the sale or exchange of a capital asset,
   then such loss shall be treated as an ordinary loss. For purposes of section 172 (relating to the net operating loss deduction) any amount of loss treated by reason of this section as an ordinary loss shall be treated as attributable to a trade or business of the taxpayer.
   (Added
   Pub. L. 85–866, title I, § 57(a)
   ,
   Sept. 2, 1958
   ,
   72 Stat. 1645
   ; amended
   Pub. L. 94–455, title XIX, § 1901(b)(3)(F)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1793
   .)
   Editorial Notes
   References in Text
   The
   Small Business Investment Act of 1958
   , referred to in cl. (1), is
   Pub. L. 85–699
   ,
   Aug. 21, 1958
   ,
   72 Stat. 689
   , which is classified principally to chapter 14B (§ 661 et seq.) of Title 15, Commerce and Trade. For complete classification of this Act to the Code, see Short Title note set out under
   section 661 of Title 15
   and Tables.
   Amendments
   1976—
   Pub. L. 94–455
   substituted “an ordinary loss” for “a loss from the sale or exchange of
   property
   which is not a capital asset”, each time appearing.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1976 Amendment
   Amendment by
   Pub. L. 94–455
   applicable with respect to taxable years beginning after
   Dec. 31, 1976
   , see
   section 1901(d) of Pub. L. 94–455
   , set out as a note under
   section 2 of this title
   .
   Effective Date
   Section applicable with respect to taxable years beginning after
   Sept. 2, 1958
   , see
   section 57(d) of Pub. L. 85–866
   , set out as an Effective Date of 1958 Amendment note under
   section 243 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/