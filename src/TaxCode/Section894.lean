/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 350533fd-c68f-451b-98ec-f7920ba5431b
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

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

inductive FilingStatus
  | Single
  | MarriedFilingJointly
  | MarriedFilingSeparately
  | HeadOfHousehold
  | QualifyingWidower
  | Estate
  | Trust
  deriving Repr, DecidableEq, Inhabited

/-!
# IRC Section 894 - Income affected by treaty

This file formalizes IRC §894 (Income affected by treaty).

## References
- [26 USC §894](https://www.law.cornell.edu/uscode/text/26/894)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 894 - Income affected by treaty
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   Treaty provisions
   (1)
   In general
   The provisions of this title shall be applied to any taxpayer with due regard to any treaty obligation of the United States which applies to such taxpayer.
   (2)
   Cross reference
   For relationship between treaties and this title, see section 7852(d).
   (b)
   Permanent establishment in United States
   For purposes of applying any exemption from, or reduction of, any tax provided by any treaty to which the United States is a party with respect to income which is not effectively connected with the conduct of a trade or business within the United States, a nonresident alien individual or a foreign corporation shall be deemed not to have a permanent establishment in the United States at any time during the taxable year. This subsection shall not apply in respect of the tax computed under section 877(b).
   (c)
   Denial of treaty benefits for certain payments through hybrid entities
   (1)
   Application to certain payments
   A foreign person shall not be entitled under any income tax treaty of the United States with a foreign country to any reduced rate of any withholding tax imposed by this title on an item of income derived through an entity which is treated as a partnership (or is otherwise treated as fiscally transparent) for purposes of this title if—
   (A)
   such item is not treated for purposes of the taxation laws of such foreign country as an item of income of such person,
   (B)
   the treaty does not contain a provision addressing the applicability of the treaty in the case of an item of income derived through a partnership, and
   (C)
   the foreign country does not impose tax on a distribution of such item of income from such entity to such person.
   (2)
   Regulations
   The Secretary shall prescribe such regulations as may be necessary or appropriate to determine the extent to which a taxpayer to which paragraph (1) does not apply shall not be entitled to benefits under any income tax treaty of the United States with respect to any payment received by, or income attributable to any activities of, an entity organized in any jurisdiction (including the United States) that is treated as a partnership or is otherwise treated as fiscally transparent for purposes of this title (including a common investment trust under section 584, a grantor trust, or an entity that is disregarded for purposes of this title) and is treated as fiscally nontransparent for purposes of the tax laws of the jurisdiction of residence of the taxpayer.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 284
   ;
   Pub. L. 89–809, title I, § 105(a)
   ,
   Nov. 13, 1966
   ,
   80 Stat. 1563
   ;
   Pub. L. 100–647, title I, § 1012(aa)(6)
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3533
   ;
   Pub. L. 105–34, title X, § 1054(a)
   ,
   Aug. 5, 1997
   ,
   111 Stat. 943
   .)
   Editorial Notes
   Amendments
   1997—Subsec. (c).
   Pub. L. 105–34
   added subsec. (c).
   1988—Subsec. (a).
   Pub. L. 100–647
   substituted “Treaty provisions” for “Income affected by treaty” in heading and amended text generally. Prior to amendment, text read as follows: “Income of any kind, to the extent required by any treaty obligation of the United States, shall not be included in gross income and shall be exempt from taxation under this subtitle.”
   1966—
   Pub. L. 89–809
   designated existing provisions as subsec. (a), added subsec. (b), and substituted “affected by treaty” for “exempt under treaty” in section catchline.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1997 Amendment
   Pub. L. 105–34, title X, § 1054(b)
   ,
   Aug. 5, 1997
   ,
   111 Stat. 944
   , provided that:
   “The amendments made by this section [amending this section] shall apply upon the date of enactment of this Act [
   Aug. 5, 1997
   ].”
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
   Effective Date of 1966 Amendment
   Pub. L. 89–809, title I, § 105(d)
   ,
   Nov. 13, 1966
   ,
   80 Stat. 1565
   , provided that:
   “The amendments made by this section (other than subsections (d) and (f)) [amending this section and enacting
   section 896 of this title
   ] shall apply with respect to taxable years beginning after
   December 31, 1966
   .”
   CFR Title
   Parts
   26
   1
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/