/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6dfdd111-8fdf-4637-bcef-33177b54befc

Aristotle encountered an error processing this file. The team has been notified.

-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0a5995d0-c4c4-47d4-809a-261627ed948b

Aristotle encountered an error processing this file. The team has been notified.

-/


import Mathlib

def Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq

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
# IRC Section 143 - Mortgage revenue bonds: qualified mortgage bond and qualified veterans’ mortgage bond

This file formalizes IRC §143 (Mortgage revenue bonds: qualified mortgage bond and qualified veterans’ mortgage bond).

## References
- [26 USC §143](https://www.law.cornell.edu/uscode/text/26/143)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 143 - Mortgage revenue bonds: qualified mortgage bond and qualified veterans’ mortgage bond
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   Qualified mortgage bond
   (1)
   Qualified mortgage bond defined
   For purposes of this title, the term “qualified
   mortgage
   bond”
   means a
   bond
   which is issued as part of a
   qualified mortgage issue
   .
   (2)
   Qualified mortgage issue defined
   (A)
   Definition
   For purposes of this title, the term “
   qualified mortgage issue
   ” means an issue by a State or political subdivision thereof of 1 or more
   bonds,
   but only if—
   (i)
   all proceeds of such issue (exclusive of issuance costs and a reasonably required reserve) are to be used to finance owner-occupied residences,
   (ii)
   such issue meets the requirements of subsections (c), (d), (e), (f), (g), (h), (i), and (m)(7),
   (iii)
   such issue does not meet the private business tests of paragraphs (1) and (2) of section 141(b), and
   (iv)
   except as provided in subparagraph (D)(ii), repayments of principal on financing provided by the issue are used not later than the close of the 1st semiannual period beginning after the date the prepayment (or complete repayment) is received to redeem
   bonds
   which are part of such issue.
   Clause (iv) shall not apply to amounts received within 10 years after the date of issuance of the issue (or, in the case of refunding
   bond
   , the date of issuance of the original
   bond
   ).
   (B)
   Good faith effort to comply with mortgage eligibility requirements
   An issue which fails to meet 1 or more of the requirements of subsections (c), (d), (e), (f), and (i) shall be treated as meeting such requirements if—
   (i)
   the issuer in good faith attempted to meet all such requirements before the
   mortgages
   were executed,
   (ii)
   95 percent or more of the proceeds devoted to owner-financing was devoted to residences with respect to which (at the time the
   mortgages
   were executed) all such requirements were met, and
   (iii)
   any failure to meet the requirements of such subsections is corrected within a reasonable period after such failure is first discovered.
   (C)
   Good faith effort to comply with other requirements
   An issue which fails to meet 1 or more of the requirements of subsections (g), (h), and (m)(7) shall be treated as meeting such requirements if—
   (i)
   the issuer in good faith attempted to meet all such requirements, and
   (ii)
   any failure to meet such requirements is due to inadvertent error after taking reasonable steps to comply with such requirements.
   (D)
   Proceeds must be used within 42 months of date of issuance
   (i)
   In general
   Except as otherwise provided in this subparagraph, an issue shall not meet the requirement of subparagraph (A)(i) unless—
   (I)
   all proceeds of the issue required to be used to finance owner-occupied residences are so used within the 42-month period beginning on the date of issuance of the issue (or, in the case of a refunding
   bond
   , within the 42-month period beginning on the date of issuance of the original
   bond
   ) or, to the extent not so used within such period, are used within such period to redeem
   bonds
   which are part of such issue, and
   (II)
   no portion of the proceeds of the issue are used to make or finance any loan (other than a loan which is a
   nonpurpose investment
   within the meaning of
   section 148(f)(6)(A)
   ) after the close of such period.
   (ii)
   Exception
   Clause (i) (and clause (iv) of subparagraph (A)) shall not be construed to require amounts of less than $250,000 to be used to redeem
   bonds
   . The Secretary may by regulation treat related issues as 1 issue for purposes of the preceding sentence.
   (b)
   Qualified veterans’ mortgage bond defined
   For purposes of this part, the term “
   qualified veterans
   ’
   mortgage
   bond” means any
   bond—
   (1)
   which is issued as part of an issue 95 percent or more of the
   net proceeds
   of which are to be used to provide residences for veterans,
   (2)
   the payment of the principal and interest on which is secured by the general obligation of a State,
   (3)
   which is part of an issue which meets the requirements of subsections (c), (g), (i)(1), and (l), and
   (4)
   which is part of an issue which does not meet the private business tests of paragraphs (1) and (2) of section 141(b).
   Rules similar to the rules of subparagraphs (B) and (C) of subsection (a)(2) shall apply to the requirements specified in paragraph (3) of this subsection.
   (c)
   Residence requirements
   (1)
   For a residence
   A residence meets the requirements of this subsection only if—
   (A)
   it is a single-family residence which can reasonably be expected to become the principal residence of the mortgagor within a reasonable time after the financing is provided, and
   (B)
   it is located within the jurisdiction of the authority issuing the
   bond
   .
   (2)
   For an issue
   An issue meets the requirements of this subsection only if all of the residences for which owner-financing is provided under the issue meet the requirements of paragraph (1).
   (d)
   3-year requirement
   (1)
   In general
   An issue meets the requirements of this subsection only if 95 percent or more of the
   net proceeds
   of such issue are used to finance the residences of mortgagors who had no present ownership interest in their principal residences at any time during the 3-year period ending on the date their
   mortgage
   is executed.
   (2)
   Exceptions
   For purposes of paragraph (1), the proceeds of an issue which are used to provide—
   (A)
   financing with respect to
   targeted area residences
   ,
   (B)
   qualified home improvement loans
   and
   qualified rehabilitation loans,
   (C)
   financing with respect to land described in subsection (i)(1)(C) and the construction of any residence thereon, and
   (D)
   in the case of
   bonds
   issued after the date of the enactment of this subparagraph, financing of any residence for a veteran (as defined in
   section 101 of title 38
   , United States Code), if such veteran has not previously qualified for and received such financing by reason of this subparagraph,
   shall be treated as used as described in paragraph (1).
   (3)
   Mortgagor’s interest in residence being financed
   For purposes of paragraph (1), a mortgagor’s interest in the residence with respect to which the financing is being provided shall not be taken into account.
   (e)
   Purchase price requirement
   (1)
   In general
   An issue meets the requirements of this subsection only if the
   acquisition cost
   of each residence the owner-financing of which is provided under the issue does not exceed 90 percent of the
   average area purchase price
   applicable to such residence.
   (2)
   Average area purchase price
   For purposes of paragraph (1), the term “
   average area purchase price
   ” means, with respect to any residence, the average purchase price of single family residences (in the
   statistical area
   in which the residence is located) which were purchased during the most recent 12-month period for which sufficient statistical information is available. The determination under the preceding sentence shall be made as of the date on which the commitment to provide the financing is made (or, if earlier, the date of the purchase of the residence).
   (3)
   Separate application to new residences and old residences
   For purposes of this subsection, the determination of
   average area purchase price
   shall be made separately with respect to—
   (A)
   residences which have not been previously occupied, and
   (B)
   residences which have been previously occupied.
   (4)
   Special rule for 2 to 4 family residences
   For purposes of this subsection, to the extent provided in regulations, the determination of
   average area purchase price
   shall be made separately with respect to 1 family, 2 family, 3 family, and 4 family residences.
   (5)
   Special rule for targeted area residences
   In the case of a
   targeted area residence
   , paragraph (1) shall be applied by substituting “110 percent” for “90 percent”.
   (6)
   Exception for qualified home improvement loans
   Paragraph (1) shall not apply with respect to any
   qualified home improvement loan
   .
   (f)
   Income requirements
   (1)
   In general
   An issue meets the requirements of this subsection only if all owner-financing provided under the issue is provided for mortgagors whose family income is 115 percent or less of the
   applicable median family income
   .
   (2)
   Determination of family income
   For purposes of this subsection, the family income of mortgagors, and area median gross income, shall be determined by the Secretary after taking into account the regulations prescribed under section 8 of the
   United States Housing Act of 1937
   (or, if such program is terminated, under such program as in effect immediately before such termination).
   (3)
   Special rule for applying paragraph (1) in the case of targeted area residences
   In the case of any financing provided under any issue for
   targeted area residences
   —
   (A)
   ⅓ of the amount of such financing may be provided without regard to paragraph (1), and
   (B)
   paragraph (1) shall be treated as satisfied with respect to the remainder of the owner financing if the family income of the mortgagor is 140 percent or less of the
   applicable median family income
   .
   (4)
   Applicable median family income
   For purposes of this subsection, the term “
   applicable median family income
   ” means, with respect to a residence, whichever of the following is the greater:
   (A)
   the area median gross income for the area in which such residence is located, or
   (B)
   the statewide median gross income for the State in which such residence is located.
   (5)
   Adjustment of income requirement based on relation of high housing costs to income
   (A)
   In general
   If the residence (for which financing is provided under the issue) is located in a
   high housing cost area
   and the limitation determined under this paragraph is greater than the limitation otherwise applicable under paragraph (1), there shall be substituted for the income limitation in paragraph (1), a limitation equal to the percentage determined under subparagraph (B) of the area median gross income for such area.
   (B)
   Income requirements for residences in high housing cost area
   The percentage determined under this subparagraph for a residence located in a
   high housing cost area
   is the percentage (not greater than 140 percent) equal to the product of—
   (I)
   115 percent, and
   (II)
   the amount by which the
   housing cost/income ratio
   for such area exceeds 0.2.
   (C)
   High housing cost areas
   For purposes of this paragraph, the term “
   high housing cost area
   ” means any
   statistical area
   for which the
   housing cost/income ratio
   is greater than 1.2.
   (D)
   Housing cost/income ratio
   For purposes of this paragraph—
   (i)
   In general
   The term “
   housing cost/income ratio
   ” means, with respect to any
   statistical area,
   the number determined by dividing—
   (I)
   the applicable housing price ratio for such area, by
   (II)
   the ratio which the area median gross income for such area bears to the median gross income for the United States.
   (ii)
   Applicable housing price ratio
   For purposes of clause (i), the applicable housing price ratio for any area is the new housing price ratio or the existing housing price ratio, whichever results in the
   housing cost/income ratio
   being closer to 1.
   (iii)
   New housing price ratio
   The new housing price ratio for any area is the ratio which—
   (I)
   the
   average area purchase price
   (as defined in subsection (e)(2)) for residences described in subsection (e)(3)(A) which are located in such area bears to
   (II)
   the average purchase price (determined in accordance with the principles of subsection (e)(2)) for residences so described which are located in the United States.
   (iv)
   Existing housing price ratio
   The existing housing price ratio for any area is the ratio determined in accordance with clause (iii) but with respect to residences described in subsection (e)(3)(B).
   (6)
   Adjustment to income requirements based on family size
   In the case of a mortgagor having a family of fewer than 3 individuals, the preceding provisions of this subsection shall be applied by substituting—
   (A)
   “100 percent” for “115 percent” each place it appears, and
   (B)
   “120 percent” for “140 percent” each place it appears.
   (g)
   Requirements related to arbitrage
   (1)
   In general
   An issue meets the requirements of this subsection only if such issue meets the requirements of paragraph (2) of this subsection and, in the case of an issue described in subsection (b)(1), such issue also meets the requirements of paragraph (3) of this subsection. Such requirements shall be in addition to the requirements of section 148.
   (2)
   Effective rate of mortgage interest cannot exceed bond yield by more than 1.125 percentage points
   (A)
   In general
   An issue shall be treated as meeting the requirements of this paragraph only if the excess of—
   (i)
   the effective rate of interest on the
   mortgages
   provided under the issue, over
   (ii)
   the yield on the issue,
   is not greater than 1.125 percentage points.
   (B)
   Effective rate of mortgage interest
   (i)
   In general
   In determining the effective rate of interest on any
   mortgage
   for purposes of this paragraph, there shall be taken into account all fees, charges, and other amounts borne by the mortgagor which are attributable to the
   mortgage
   or to the
   bond
   issue.
   (ii)
   Specification of some of the amounts to be treated as borne by the mortgagor
   For purposes of clause (i), the following items (among others) shall be treated as borne by the mortgagor:
   (I)
   all points or similar charges paid by the seller of the property, and
   (II)
   the excess of the amounts received from any person other than the mortgagor by any person in connection with the acquisition of the mortgagor’s interest in the property over the usual and reasonable
   acquisition costs
   of a person acquiring like property where owner-financing is not provided through the use of qualified
   mortgage
   bonds or
   qualified veterans
   ’
   mortgage
   bonds.
   (iii)
   Specification of some of the amounts to be treated as not borne by the mortgagor
   For purposes of clause (i), the following items shall not be taken into account:
   (I)
   any expected rebate of arbitrage profits, and
   (II)
   any application fee, survey fee, credit report fee, insurance charge, or similar amount to the extent such amount does not exceed amounts charged in such area in cases where owner-financing is not provided through the use of qualified
   mortgage
   bonds
   or
   qualified veterans
   ’
   mortgage
   bonds.
   Subclause (II) shall not apply to origination fees, points, or similar amounts.
   (iv)
   Prepayment assumptions
   In determining the effective rate of interest—
   (I)
   it shall be assumed that the
   mortgage
   prepayment rate will be the rate set forth in the most recent applicable
   mortgage
   maturity experience table published by the Federal Housing Administration, and
   (II)
   prepayments of principal shall be treated as received on the last day of the month in which the issuer reasonably expects to receive such prepayments.
   The Secretary may by regulation adjust the
   mortgage
   prepayment rate otherwise used in determining the effective rate of interest to the extent the Secretary determines that such an adjustment is appropriate by reason of the impact of subsection (m).
   (C)
   Yield on the issue
   For purposes of this subsection, the yield on an issue shall be determined on the basis of—
   (i)
   the issue price (within the meaning of sections
   1273
   and
   1274
   ), and
   (ii)
   an expected maturity for the
   bonds
   which is consistent with the assumptions required under subparagraph (B)(iv).
   (3)
   Arbitrage and investment gains to be used to reduce costs of owner-financing
   (A)
   In general
   An issue shall be treated as meeting the requirements of this paragraph only if an amount equal to the sum of—
   (i)
   the excess of—
   (I)
   the amount earned on all
   nonpurpose investments
   (other than investments attributable to an excess described in this clause), over
   (II)
   the amount which would have been earned if such investments were invested at a rate equal to the yield on the issue, plus
   (ii)
   any income attributable to the excess described in clause (i),
   is paid or credited to the mortgagors as rapidly as may be practicable.
   (B)
   Investment gains and losses
   For purposes of subparagraph (A), in determining the amount earned on all
   nonpurpose investments
   , any gain or loss on the
   disposition
   of such investments shall be taken into account.
   (C)
   Reduction where issuer does not use full 1.125 percentage points under paragraph (2)
   (i)
   In general
   The amount required to be paid or credited to mortgagors under subparagraph (A) (determined under this paragraph without regard to this subparagraph) shall be reduced by the unused paragraph (2) amount.
   (ii)
   Unused paragraph (2) amount
   For purposes of clause (i), the unused paragraph (2) amount is the amount which (if it were treated as an interest payment made by mortgagors) would result in the excess referred to in paragraph (2)(A) being equal to 1.125 percentage points. Such amount shall be fixed and determined as of the yield determination date.
   (D)
   Election to pay United States
   Subparagraph (A) shall be satisfied with respect to any issue if the issuer elects before issuing the
   bonds
   to pay over to the United States—
   (i)
   not less frequently than once each 5 years after the date of issue, an amount equal to 90 percent of the aggregate amount which would be required to be paid or credited to mortgagors under subparagraph (A) (and not theretofore paid to the United States), and
   (ii)
   not later than 60 days after the redemption of the last
   bond
   , 100 percent of such aggregate amount not theretofore paid to the United States.
   (E)
   Simplified accounting
   The Secretary shall permit any simplified system of accounting for purposes of this paragraph which the issuer establishes to the satisfaction of the Secretary will assure that the purposes of this paragraph are carried out.
   (F)
   Nonpurpose investment
   For purposes of this paragraph, the term “
   nonpurpose investment
   ” has the meaning given such term by section 148(f)(6)(A).
   (h)
   Portion of loans required to be placed in targeted areas
   (1)
   In general
   An issue meets the requirements of this subsection only if at least 20 percent of the proceeds of the issue which are devoted to providing owner-financing is made available (with reasonable diligence) for owner-financing of
   targeted area residences
   for at least 1 year after the date on which owner-financing is first made available with respect to
   targeted area residences
   .
   (2)
   Limitation
   Nothing in paragraph (1) shall be treated as requiring the making available of an amount which exceeds 40 percent of the average annual aggregate principal amount of
   mortgages
   executed during the immediately preceding 3 calendar years for single-family, owner-occupied residences located in targeted areas within the jurisdiction of the issuing authority.
   (i)
   Other requirements
   (1)
   Mortgages must be new mortgages
   (A)
   In general
   An issue meets the requirements of this subsection only if no part of the proceeds of such issue is used to acquire or replace existing
   mortgages
   .
   (B)
   Exceptions
   Under regulations prescribed by the Secretary, the replacement of—
   (i)
   construction period loans,
   (ii)
   bridge loans or similar temporary initial financing, and
   (iii)
   in the case of a
   qualified rehabilitation
   , an existing
   mortgage,
   shall not be treated as the acquisition or replacement of an existing
   mortgage
   for purposes of subparagraph (A).
   (C)
   Exception for certain contract for deed agreements
   (i)
   In general
   In the case of land possessed under a
   contract for deed
   by a mortgagor—
   (I)
   whose principal residence (within the meaning of
   section 121
   ) is located on such land, and
   (II)
   whose family income (as defined in subsection (f)(2)) is not more than 50 percent of
   applicable median family income
   (as defined in subsection (f)(4)),
   the
   contract for deed
   shall not be treated as an existing
   mortgage
   for purposes of subparagraph (A).
   (ii)
   Contract for deed defined
   For purposes of this subparagraph, the term “
   contract for deed
   ” means a seller-financed contract for the conveyance of land under which—
   (I)
   legal title does not pass to the purchaser until the consideration under the contract is fully paid to the seller, and
   (II)
   the seller’s remedy for nonpayment is forfeiture rather than judicial or nonjudicial foreclosure.
   (2)
   Certain requirements must be met where mortgage is assumed
   An issue meets the requirements of this subsection only if each
   mortgage
   with respect to which owner-financing has been provided under such issue may be assumed only if the requirements of subsections (c), (d), and (e), and the requirements of paragraph (1) or (3)(B) of subsection (f) (whichever applies), are met with respect to such assumption.
   (j)
   Targeted area residences
   (1)
   In general
   For purposes of this section, the term “
   targeted area residence
   ” means a residence in an area which is either—
   (A)
   a
   qualified census tract
   , or
   (B)
   an
   area of chronic economic distress
   .
   (2)
   Qualified census tract
   (A)
   In general
   For purposes of paragraph (1), the term “
   qualified census tract
   ” means a census tract in which 70 percent or more of the families have income which is 80 percent or less of the statewide median family income.
   (B)
   Data used
   The determination under subparagraph (A) shall be made on the basis of the most recent decennial census for which data are available.
   (3)
   Area of chronic economic distress
   (A)
   In general
   For purposes of paragraph (1), the term “
   area of chronic economic distress
   ” means an
   area of chronic economic distress
   —
   (i)
   designated by the State as meeting the standards established by the State for purposes of this subsection, and
   (ii)
   the designation of which has been approved by the Secretary and the Secretary of Housing and Urban Development.
   (B)
   Criteria to be used in approving State designations
   The criteria used by the Secretary and the Secretary of Housing and Urban Development in evaluating any proposed designation of an area for purposes of this subsection shall be—
   (i)
   the condition of the housing stock, including the age of the housing and the number of abandoned and substandard residential units,
   (ii)
   the need of area residents for owner-financing under this section, as indicated by low per capita income, a high percentage of families in poverty, a high number of welfare recipients, and high unemployment rates,
   (iii)
   the potential for use of owner-financing under this section to improve housing conditions in the area, and
   (iv)
   the existence of a housing assistance plan which provides a displacement program and a public improvements and services program.
   (k)
   Other definitions and special rules
   For purposes of this section—
   (1)
   Mortgage
   The term “
   mortgage
   ” means any owner-financing.
   (2)
   Statistical area
   (A)
   In general
   The term “
   statistical area
   ” means—
   (i)
   a
   metropolitan statistical area
   , and
   (ii)
   any county (or the portion thereof) which is not within a
   metropolitan statistical area
   .
   (B)
   Metropolitan statistical area
   The term “
   metropolitan statistical area
   ” includes the area defined as such by the
   Secretary of Commerce
   .
   (C)
   Designation where adequate statistical information not available
   For purposes of this paragraph, if there is insufficient recent statistical information with respect to a county (or portion thereof) described in subparagraph (A)(ii), the Secretary may substitute for such county (or portion thereof) another area for which there is sufficient recent statistical information.
   (D)
   Designation where no county
   In the case of any portion of a State which is not within a county, subparagraphs (A)(ii) and (C) shall be applied by substituting for “county” an area designated by the Secretary which is the equivalent of a county.
   (3)
   Acquisition cost
   (A)
   In general

-- TODO: Add type definitions
-- TODO: Add main functions