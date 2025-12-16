/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: e86f6758-e3dc-452d-b68d-539b38846331
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
# IRC Section 2015 - Credit for death taxes on remainders

This file formalizes IRC §2015 (Credit for death taxes on remainders).

## References
- [26 USC §2015](https://www.law.cornell.edu/uscode/text/26/2015)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2015 - Credit for death taxes on remainders
   U.S. Code
   Notes
   prev
   |
   next
   Where an election is made under section 6163(a) to postpone payment of the tax imposed by section 2001, or 2101, such part of any estate, inheritance, legacy, or succession taxes allowable as a credit under section 2014, as is attributable to a reversionary or remainder interest may be allowed as a credit against the tax attributable to such interest, subject to the limitations on the amount of the credit contained in such sections, if such part is paid, and credit therefor claimed, at any time before the expiration of the time for payment of the tax imposed by section 2001 or 2101 as postponed and extended under section 6163.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 379
   ;
   Pub. L. 85–866, title I, § 66(a)(1)
   ,
   Sept. 2, 1958
   ,
   72 Stat. 1657
   ;
   Pub. L. 107–16, title V, § 532(c)(4)
   ,
   June 7, 2001
   ,
   115 Stat. 74
   .)
   Editorial Notes
   Amendments
   2001—
   Pub. L. 107–16
   struck out “2011 or” before “2014”.
   1958—
   Pub. L. 85–866
   substituted “the time for payment of the tax imposed by section 2001 or 2101 as postponed and extended under section 6163” for “60 days after the termination of the precedent interest or interests in the property”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 2001 Amendment
   Amendment by
   Pub. L. 107–16
   applicable to estates of decedents dying, and generation-skipping transfers, after
   Dec. 31, 2004
   , see
   section 532(d) of Pub. L. 107–16
   , set out as a note under
   section 2012 of this title
   .
   Effective Date of 1958 Amendment
   Pub. L. 85–866, title I, § 66(a)(3)
   ,
   Sept. 2, 1958
   ,
   72 Stat. 1658
   , provided that:
   “The amendments made by paragraphs (1) and (2) [amending this section and section 927 of I.R.C. 1939] shall apply in the case of any reversionary or remainder interest in property only if the precedent interest or interests in the property did not terminate before the beginning of the 60-day period which ends on the date of the enactment of this Act [
   Sept. 2, 1958
   ].”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/