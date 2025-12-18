/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d4fee672-bd8a-46e2-b08b-8db9a3300105
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
# IRC Section 1359 - Disposition of qualifying vessels

This file formalizes IRC §1359 (Disposition of qualifying vessels).

## References
- [26 USC §1359](https://www.law.cornell.edu/uscode/text/26/1359)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1359 - Disposition of qualifying vessels
   U.S. Code
   Notes
   prev
   | next
   (a)
   In general
   If any
   qualifying vessel operator
   sells or disposes of any
   qualifying vessel
   in an otherwise taxable transaction, at the election of such operator, no gain shall be recognized if any replacement
   qualifying vessel
   is acquired during the period specified in subsection (b), except to the extent that the amount realized upon such sale or
   disposition
   exceeds the cost of the replacement
   qualifying vessel.
   (b)
   Period within which property must be replaced
   The period referred to in subsection (a) shall be the period beginning one year prior to the
   disposition
   of the
   qualifying vessel
   and ending—
   (1)
   3 years after the close of the first taxable year in which the gain is realized, or
   (2)
   subject to such terms and conditions as may be specified by the Secretary, on such later date as the Secretary may designate on application by the taxpayer.
   Such application shall be made at such time and in such manner as the Secretary may by regulations prescribe.
   (c)
   Application of section to noncorporate operators
   For purposes of this section, the term “
   qualifying vessel operator
   ” includes any person who would be a
   qualifying vessel operator
   were such person a corporation.
   (d)
   Time for assessment of deficiency attributable to gain
   If a
   qualifying vessel operator
   has made the election provided in subsection (a), then—
   (1)
   the statutory period for the assessment of any deficiency, for any taxable year in which any part of the gain is realized, attributable to such gain shall not expire prior to the expiration of 3 years from the date the Secretary is notified by such operator (in such manner as the Secretary may by regulations prescribe) of the replacement
   qualifying vessel
   or of an intention not to replace, and
   (2)
   such deficiency may be assessed before the expiration of such 3-year period notwithstanding the provisions of
   section 6212(c)
   or the provisions of any other law or rule of law which would otherwise prevent such assessment.
   (e)
   Basis of replacement qualifying vessel
   In the case of any replacement
   qualifying vessel
   purchased by the
   qualifying vessel operator
   which resulted in the nonrecognition of any part of the gain realized as the result of a sale or other
   disposition
   of a
   qualifying vessel,
   the basis shall be the cost of the replacement
   qualifying vessel
   decreased in the amount of the gain not so recognized; and if the property purchased consists of more than one piece of property, the basis determined under this sentence shall be allocated to the purchased properties in proportion to their respective costs.
   (Added
   Pub. L. 108–357, title II, § 248(a)
   ,
   Oct. 22, 2004
   ,
   118 Stat. 1456
   .)
   Statutory Notes and Related Subsidiaries
   Effective Date
   Section applicable to taxable years beginning after
   Oct. 22, 2004
   , see
   section 248(c) of Pub. L. 108–357
   , set out as an Effective Date of 2004 Amendments note under
   section 56 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/