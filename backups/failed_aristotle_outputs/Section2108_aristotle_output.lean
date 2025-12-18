/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: db5e8cf7-2b8e-48c0-9eeb-c416b32668c9
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
# IRC Section 2108 - Application of pre-1967 estate tax provisions

This file formalizes IRC §2108 (Application of pre-1967 estate tax provisions).

## References
- [26 USC §2108](https://www.law.cornell.edu/uscode/text/26/2108)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2108 - Application of pre-1967 estate tax provisions
   U.S. Code
   Notes
   prev
   | next
   (a)
   Imposition of more burdensome tax by foreign country
   Whenever the President finds that—
   (1)
   under the laws of any foreign country, considering the tax system of such foreign country, a more burdensome tax is imposed by such foreign country on the transfer of estates of decedents who were citizens of the United States and not residents of such foreign country than the tax imposed by this subchapter on the transfer of estates of decedents who were residents of such foreign country,
   (2)
   such foreign country, when requested by the United States to do so, has not acted to revise or reduce such tax so that it is no more burdensome than the tax imposed by this subchapter on the transfer of estates of decedents who were residents of such foreign country, and
   (3)
   it is in the public interest to apply pre-1967 tax provisions in accordance with this section to the transfer of estates of decedents who were residents of such foreign country,
   the President shall proclaim that the tax on the transfer of the estate of every decedent who was a resident of such foreign country at the time of his death shall, in the case of decedents dying after the date of such proclamation, be determined under this subchapter without regard to amendments made to sections 2101 (relating to tax imposed), 2102 (relating to credits against tax), 2106 (relating to taxable estate), and 6018 (relating to estate tax returns) on or after
   November 13, 1966
   .
   (b)
   Alleviation of more burdensome tax
   Whenever the President finds that the laws of any foreign country with respect to which the President has made a proclamation under subsection (a) have been modified so that the tax on the transfer of estates of decedents who were citizens of the United States and not residents of such foreign country is no longer more burdensome than the tax imposed by this subchapter on the transfer of estates of decedents who were residents of such foreign country, he shall proclaim that the tax on the transfer of the estate of every decedent who was a resident of such foreign country at the time of his death shall, in the case of decedents dying after the date of such proclamation, be determined under this subchapter without regard to subsection (a).
   (c)
   Notification of
   Congress
   required
   No proclamation shall be issued by the President pursuant to this section unless, at least 30 days prior to such proclamation, he has notified the
   Senate
   and the
   House of Representatives
   of his intention to issue such proclamation.
   (d)
   Implementation by regulations
   The Secretary shall prescribe such regulations as may be necessary or appropriate to implement this section.
   (Added
   Pub. L. 89–809, title I, § 108(f)
   ,
   Nov. 13, 1966
   ,
   80 Stat. 1573
   ; amended
   Pub. L. 94–455, title XIX
   , §§ 1902(a)(6), 1906(b)(13)(A),
   Oct. 4, 1976
   ,
   90 Stat. 1805
   , 1834.)
   Editorial Notes
   Amendments
   1976—Subsec. (a).
   Pub. L. 94–455, § 1902(a)(6)
   , substituted “
   November 13, 1976
   ” for “the date of enactment of this section” after “on or after”.
   Subsec. (d).
   Pub. L. 94–455, § 1906(b)(13)(A)
   , struck out “or his delegate” after “Secretary”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1976 Amendment
   Amendment by
   section 1902(a)(6) of Pub. L. 94–455
   applicable in the case of estates of decedents dying after
   Oct. 4, 1976
   , see
   section 1902(c)(1) of Pub. L. 94–455
   , set out as a note under
   section 2012 of this title
   .
   Effective Date
   Section applicable with respect to estates of decedents dying after
   Nov. 13, 1966
   , see
   section 108(i) of Pub. L. 89–809
   , set out as an Effective Date of 1966 Amendment note under
   section 2101 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/