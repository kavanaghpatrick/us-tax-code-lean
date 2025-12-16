/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b50e52da-39be-461f-96dc-1a032ecef7ad
-/

import Mathlib


set_option linter.mathlibStandardSet false

open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

-- Common definitions for US Tax Code formalization
def Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

inductive FilingStatus
  | Single                         -- IRC §1(c)
  | MarriedFilingJointly          -- IRC §1(a)
  | MarriedFilingSeparately       -- IRC §1(d)
  | HeadOfHousehold               -- IRC §1(b)
  | QualifyingWidower             -- IRC §2(b)
  | Estate                         -- IRC §1(e)(1)
  | Trust                          -- IRC §1(e)(2)
  deriving Repr, DecidableEq, Inhabited

structure Taxpayer where
  id : String
  filingStatus : FilingStatus
  taxYear : TaxYear

/-!
# IRC Section 198 - Expensing of environmental remediation costs

This file formalizes IRC §198 (Expensing of environmental remediation costs).

## References
- [26 USC §198](https://www.law.cornell.edu/uscode/text/26/198)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 198 - Expensing of environmental remediation costs
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   In general
   A taxpayer may elect to treat any
   qualified environmental remediation expenditure
   which is paid or incurred by the taxpayer as an expense which is not chargeable to capital account. Any expenditure which is so treated shall be allowed as a deduction for the taxable year in which it is paid or incurred.
   (b)
   Qualified environmental remediation expenditure
   For purposes of this section—
   (1)
   In general
   The term “
   qualified environmental remediation expenditure
   ” means any expenditure—
   (A)
   which is otherwise chargeable to capital account, and
   (B)
   which is paid or incurred in connection with the abatement or control of
   hazardous substances
   at a
   qualified contaminated site
   .
   (2)
   Special rule for expenditures for depreciable property
   Such term shall not include any expenditure for the acquisition of property of a character subject to the allowance for depreciation which is used in connection with the abatement or control of
   hazardous substances
   at a
   qualified contaminated site
   ; except that the portion of the allowance under
   section 167
   for such property which is otherwise allocated to such site shall be treated as a
   qualified environmental remediation expenditure.
   (c)
   Qualified contaminated site
   For purposes of this section—
   (1)
   In general
   The term “
   qualified contaminated site
   ” means any area—
   (A)
   which is held by the taxpayer for use in a trade or business or for the production of income, or which is property described in section 1221(a)(1) in the hands of the taxpayer, and
   (B)
   at or on which there has been a release (or threat of release) or disposal of any
   hazardous substance
   .
   (2)
   National priorities listed sites not included
   Such term shall not include any site which is on, or proposed for, the national priorities list under section 105(a)(8)(B) of the Comprehensive Environmental Response, Compensation, and Liability Act of 1980 (as in effect on the date of the enactment of this section).
   (3)
   Taxpayer must receive statement from State environmental agency
   An area shall be treated as a
   qualified contaminated site
   with respect to expenditures paid or incurred during any taxable year only if the taxpayer receives a statement from the appropriate agency of the State in which such area is located that such area meets the requirement of paragraph (1)(B).
   (4)
   Appropriate State agency
   For purposes of paragraph (3), the chief executive officer of each State may, in consultation with the Administrator of the
   Environmental Protection Agency
   , designate the appropriate State environmental agency within 60 days of the date of the enactment of this section. If the chief executive officer of a State has not designated an appropriate environmental agency within such 60-day period, the appropriate environmental agency for such State shall be designated by the Administrator of the
   Environmental Protection Agency
   .
   (d)
   Hazardous substance
   For purposes of this section—
   (1)
   In general
   The term “
   hazardous substance
   ” means—
   (A)
   any substance which is a
   hazardous substance
   as defined in section 101(14) of the Comprehensive Environmental Response, Compensation, and Liability Act of 1980,
   (B)
   any substance which is designated as a
   hazardous substance
   under section 102 of such Act, and
   (C)
   any petroleum product (as defined in
   section 4612(a)(3)
   ).
   (2)
   Exception
   Such term shall not include any substance with respect to which a removal or remedial action is not permitted under section 104 of such Act by reason of subsection (a)(3) thereof.
   (e)
   Deduction recaptured as ordinary income on sale, etc.
   Solely for purposes of section 1245, in the case of property to which a
   qualified environmental remediation expenditure
   would have been capitalized but for this section—
   (1)
   the deduction allowed by this section for such expenditure shall be treated as a deduction for depreciation, and
   (2)
   such property (if not otherwise
   section 1245
   property) shall be treated as section 1245 property solely for purposes of applying section 1245 to such deduction.
   (f)
   Coordination with other provisions
   Sections
   280B
   and
   468
   shall not apply to amounts which are treated as expenses under this section.
   (g)
   Regulations
   The Secretary shall prescribe such regulations as may be necessary or appropriate to carry out the purposes of this section.
   (h)
   Termination
   This section shall not apply to expenditures paid or incurred after
   December 31, 2011
   .
   (Added
   Pub. L. 105–34, title IX, § 941(a)
   ,
   Aug. 5, 1997
   ,
   111 Stat. 882
   ; amended
   Pub. L. 106–170, title V
   , §§ 511, 532(c)(2)(A),
   Dec. 17, 1999
   ,
   113 Stat. 1924
   , 1930;
   Pub. L. 106–554, § 1(a)(7) [title I, § 162(a), (b)]
   ,
   Dec. 21, 2000
   ,
   114 Stat. 2763
   , 2763A–625;
   Pub. L. 108–311, title III, § 308(a)
   ,
   Oct. 4, 2004
   ,
   118 Stat. 1179
   ;
   Pub. L. 109–432, div. A, title I, § 109(a)
   , (b),
   Dec. 20, 2006
   ,
   120 Stat. 2939
   ;
   Pub. L. 110–343, div. C, title III, § 318(a)
   ,
   Oct. 3, 2008
   ,
   122 Stat. 3873
   ;
   Pub. L. 111–312, title VII, § 745(a)
   ,
   Dec. 17, 2010
   ,
   124 Stat. 3319
   .)
   Editorial Notes
   References in Text
   The date of the enactment of this section, referred to in subsec. (c)(2), (4), is the date of enactment of
   Pub. L. 105–34
   , which was approved
   Aug. 5, 1997
   .
   Sections 101(14), 102, 104, and 105(a)(8)(B) of the Comprehensive Environmental Response, Compensation, and Liability Act of 1980, referred to in subsecs. (c)(2) and (d), are classified to sections 9601(14), 9602, 9604, and 9605(a)(8)(B), respectively, of Title 42, The Public Health and Welfare.
   Amendments
   2010—Subsec. (h).
   Pub. L. 111–312
   substituted “
   December 31, 2011
   ” for “
   December 31, 2009
   ”.
   2008—Subsec. (h).
   Pub. L. 110–343
   substituted “
   December 31, 2009
   ” for “
   December 31, 2007
   ”.
   2006—Subsec. (d)(1)(C).
   Pub. L. 109–432, § 109(b)
   , added subpar. (C).
   Subsec. (h).
   Pub. L. 109–432, § 109(a)
   , substituted “2007” for “2005”.
   2004—Subsec. (h).
   Pub. L. 108–311
   substituted “2005” for “2003”.
   2000—Subsec. (c).
   Pub. L. 106–554, § 1(a)(7) [title I, § 162(a)]
   , amended subsec. (c) generally. Prior to amendment, subsec. (c) defined the term
   “qualified contaminated site”
   to include certain property described in
   section 1221(a)(1) of this title
   , within a targeted area, and at which there had been a release or disposal of any
   hazardous substance,
   provided that an area could be treated as a
   qualified contaminated site
   only if the taxpayer received a certain statement from an appropriate State agency, provided for designation of appropriate State agencies, and defined targeted area.
   Subsec. (h).
   Pub. L. 106–554, § 1(a)(7) [title I, § 162(b)]
   , substituted “2003” for “2001”.
   1999—Subsec. (c)(1)(A)(i).
   Pub. L. 106–170, § 532(c)(2)(A)
   , substituted “section 1221(a)(1)” for “section 1221(1)”.
   Subsec. (h).
   Pub. L. 106–170, § 511
   , substituted “2001” for “2000”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 2010 Amendment
   Pub. L. 111–312, title VII, § 745(b)
   ,
   Dec. 17, 2010
   ,
   124 Stat. 3319
   , provided that:
   “The amendment made by this section [amending this section] shall apply to expenditures paid or incurred after
   December 31, 2009
   .”
   Effective Date of 2008 Amendment
   Pub. L. 110–343, div. C, title III, § 318(b)
   ,
   Oct. 3, 2008
   ,
   122 Stat. 3873
   , provided that:
   “The amendment made by this section [amending this section] shall apply to expenditures paid or incurred after
   December 31, 2007
   .”
   Effective Date of 2006 Amendment
   Pub. L. 109–432, div. A, title I, § 109(c)
   ,
   Dec. 20, 2006
   ,
   120 Stat. 2939
   , provided that:
   “The amendments made by this section [amending this section] shall apply to expenditures paid or incurred after
   December 31, 2005
   .”
   Effective Date of 2004 Amendment
   Pub. L. 108–311, title III, § 308(b)
   ,
   Oct. 4, 2004
   ,
   118 Stat. 1179
   , provided that:
   “The amendment made by subsection (a) [amending this section] shall apply to expenditures paid or incurred after
   December 31, 2003
   .”
   Effective Date of 2000 Amendment
   Pub. L. 106–554, § 1(a)(7) [title I, § 162(c)]
   ,
   Dec. 21, 2000
   ,
   114 Stat. 2763
   , 2763A–625, provided that:
   “The amendments made by this section [amending this section] shall apply to expenditures paid or incurred after the date of the enactment of this Act [
   Dec. 21, 2000
   ].”
   Effective Date of 1999 Amendment
   Amendment by
   section 532(c)(2)(A) of Pub. L. 106–170
   applicable to any instrument held, acquired, or entered into, any transaction entered into, and supplies held or acquired on or after
   Dec. 17, 1999
   , see
   section 532(d) of Pub. L. 106–170
   , set out as a note under
   section 170 of this title
   .
   Effective Date
   Pub. L. 105–34, title IX, § 941(c)
   ,
   Aug. 5, 1997
   ,
   111 Stat. 885
   , provided that:
   “The amendments made by this section [enacting this section] shall apply to expenditures paid or incurred after the date of the enactment of this Act [
   Aug. 5, 1997
   ], in taxable years ending after such date.”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/