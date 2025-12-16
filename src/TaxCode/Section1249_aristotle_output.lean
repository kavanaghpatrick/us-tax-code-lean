/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1ba21757-0307-409c-86f9-75232c158319
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
# IRC Section 1249 - Gain from certain sales or exchanges of patents, etc., to foreign corporations

This file formalizes IRC §1249 (Gain from certain sales or exchanges of patents, etc., to foreign corporations).

## References
- [26 USC §1249](https://www.law.cornell.edu/uscode/text/26/1249)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1249 - Gain from certain sales or exchanges of patents, etc., to foreign corporations
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   Gain from the sale or exchange of a patent, an invention, model, or design (whether or not patented), a copyright, a secret formula or process, or any other similar
   property
   right to any foreign corporation by any United States person (as defined in
   section 7701(a)(30)
   ) which controls such foreign corporation shall, if such gain would (but for the provisions of this subsection) be gain from the sale or exchange of a capital asset or of
   property
   described in section 1231, be considered as ordinary income.
   (b)
   Control
   For purposes of subsection (a), control means, with respect to any foreign corporation, the ownership, directly or indirectly, of
   stock
   possessing more than 50 percent of the total combined voting power of all classes of
   stock
   entitled to vote. For purposes of this subsection, the rules for determining ownership of
   stock
   prescribed by
   section 958
   shall apply.
   (Added
   Pub. L. 87–834, § 16(a)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 1045
   ; amended
   Pub. L. 89–809, title I, § 104(m)(3)
   ,
   Nov. 13, 1966
   ,
   80 Stat. 1563
   ;
   Pub. L. 94–455, title XIX, § 1901(b)(3)(K)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1793
   ;
   Pub. L. 113–295, div. A, title II, § 221(a)(84)
   ,
   Dec. 19, 2014
   ,
   128 Stat. 4049
   .)
   Editorial Notes
   Amendments
   2014—Subsec. (a).
   Pub. L. 113–295
   struck out “after
   December 31, 1962
   ,” before “of a patent”.
   1976—Subsec. (a).
   Pub. L. 94–455
   substituted “ordinary income” for “gain from the sale or exchange of
   property
   which is neither a capital asset nor
   property
   described in section 1231”.
   1966—Subsec. (a).
   Pub. L. 89–809
   substituted “Gain” for “Except as provided in subsection (c), gain”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 2014 Amendment
   Amendment by
   Pub. L. 113–295
   effective
   Dec. 19, 2014
   , subject to a savings provision, see
   section 221(b) of Pub. L. 113–295
   , set out as a note under
   section 1 of this title
   .
   Effective Date of 1976 Amendment
   Amendment by
   Pub. L. 94–455
   effective for taxable years beginning after
   Dec. 31, 1976
   , see
   section 1901(d) of Pub. L. 94–455
   , set out as a note under
   section 2 of this title
   .
   Effective Date of 1966 Amendment
   Amendment by
   Pub. L. 89–809
   applicable with respect to taxable years beginning after
   Dec. 31, 1966
   , see
   section 104(n) of Pub. L. 89–809
   , set out as a note under
   section 11 of this title
   .
   Effective Date
   Pub. L. 87–834, § 16(c)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 1045
   , provided that:
   “The amendments made by this section [enacting this section] shall apply to taxable years beginning after
   December 31, 1962
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/