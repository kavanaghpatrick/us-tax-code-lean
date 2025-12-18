/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 14686445-8a26-489c-9e0a-a781ca4eeb23

Aristotle encountered an error processing this file. The team has been notified.

-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: fb3a7e3a-2cec-433f-b8f4-c15826a5e22d

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
# IRC Section 42 - Low-income housing credit

This file formalizes IRC §42 (Low-income housing credit).

## References
- [26 USC §42](https://www.law.cornell.edu/uscode/text/26/42)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 42 - Low-income housing credit
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   In general
   For purposes of section 38, the amount of the low-income housing credit determined under this section for any taxable year in the
   credit period
   shall be an amount equal to—
   (1)
   the
   applicable percentage
   of
   (2)
   the qualified basis of each
   qualified low-income building
   .
   (b)
   Applicable percentage: 70 percent present value credit for certain new buildings; 30 percent present value credit for certain other buildings
   (1)
   Determination of applicable percentage
   For purposes of this section—
   (A)
   In general
   The term “
   applicable percentage
   ” means, with respect to any building, the appropriate percentage prescribed by the Secretary for the earlier of—
   (i)
   the month in which such building is placed in service, or
   (ii)
   at the election of the taxpayer—
   (I)
   the month in which the taxpayer and the
   housing credit agency
   enter into an agreement with respect to such building (which is binding on such agency, the taxpayer, and all successors in interest) as to the housing credit dollar amount to be allocated to such building, or
   (II)
   in the case of any building to which subsection (h)(4)(B) applies, the month in which the tax-exempt obligations are issued.
   A month may be elected under clause (ii) only if the election is made not later than the 5th day after the close of such month. Such an election, once made, shall be irrevocable.
   (B)
   Method of prescribing percentages
   The percentages prescribed by the Secretary for any month shall be percentages which will yield over a 10-year period amounts of credit under subsection (a) which have a present value equal to—
   (i)
   70 percent of the qualified basis of a
   new building
   which is not federally subsidized for the taxable year, and
   (ii)
   30 percent of the qualified basis of a building not described in clause (i).
   (C)
   Method of discounting
   The present value under subparagraph (B) shall be determined—
   (i)
   as of the last day of the 1st year of the 10-year period referred to in subparagraph (B),
   (ii)
   by using a discount rate equal to 72 percent of the average of the annual Federal mid-term rate and the annual Federal long-term rate applicable under
   section 1274(d)(1)
   to the month applicable under clause (i) or (ii) of subparagraph (A) and compounded annually, and
   (iii)
   by assuming that the credit allowable under this section for any year is received on the last day of such year.
   (2)
   Minimum credit rate for non-federally subsidized new buildings
   In the case of any
   new building
   —
   (A)
   which is placed in service by the taxpayer after the date of the enactment of this paragraph, and
   (B)
   which is not federally subsidized for the taxable year,
   the
   applicable percentage
   shall not be less than 9 percent.
   (3)
   Minimum credit rate
   In the case of any new or
   existing building
   to which paragraph (2) does not apply and which is placed in service by the taxpayer after
   December 31, 2020
   , the
   applicable percentage
   shall not be less than 4 percent.
   (4)
   Cross references
   (A)
   For treatment of certain
   rehabilitation expenditures
   as separate
   new buildings
   , see subsection (e).
   (B)
   For determination of
   applicable percentage
   for increases in qualified basis after the 1st year of the
   credit period,
   see subsection (f)(3).
   (C)
   For authority of
   housing credit agency
   to limit
   applicable percentage
   and qualified basis which may be taken into account under this section with respect to any building, see subsection (h)(7).
   (c)
   Qualified basis; qualified low-income building
   For purposes of this section—
   (1)
   Qualified basis
   (A)
   Determination
   The qualified basis of any
   qualified low-income building
   for any taxable year is an amount equal to—
   (i)
   the
   applicable fraction
   (determined as of the close of such taxable year) of
   (ii)
   the eligible basis of such building (determined under subsection (d)(5)).
   (B)
   Applicable fraction
   For purposes of subparagraph (A), the term “
   applicable fraction
   ” means the smaller of the
   unit fraction
   or the
   floor space fraction
   .
   (C)
   Unit fraction
   For purposes of subparagraph (B), the term “
   unit fraction
   ” means the fraction—
   (i)
   the numerator of which is the number of
   low-income units
   in the building, and
   (ii)
   the denominator of which is the number of residential rental units (whether or not occupied) in such building.
   (D)
   Floor space fraction
   For purposes of subparagraph (B), the term “
   floor space fraction
   ” means the fraction—
   (i)
   the numerator of which is the total floor space of the
   low-income units
   in such building, and
   (ii)
   the denominator of which is the total floor space of the residential rental units (whether or not occupied) in such building.
   (E)
   Qualified basis to include portion of building used to provide supportive services for homeless
   In the case of a
   qualified low-income building
   described in subsection (i)(3)(B)(iii), the qualified basis of such building for any taxable year shall be increased by the lesser of—
   (i)
   so much of the eligible basis of such building as is used throughout the year to provide
   supportive services
   designed to assist tenants in locating and retaining permanent housing, or
   (ii)
   20 percent of the qualified basis of such building (determined without regard to this subparagraph).
   (2)
   Qualified low-income building
   The term “
   qualified low-income building
   ” means any building—
   (A)
   which is part of a
   qualified low-income housing project
   at all times during the period—
   (i)
   beginning on the 1st day in the
   compliance period
   on which such building is part of such a project, and
   (ii)
   ending on the last day of the
   compliance period
   with respect to such building, and
   (B)
   to which the amendments made by section 201(a) of the
   Tax Reform Act of 1986
   apply.
   (d)
   Eligible basis
   For purposes of this section—
   (1)
   New buildings
   The eligible basis of a
   new building
   is its adjusted basis as of the close of the 1st taxable year of the
   credit period
   .
   (2)
   Existing buildings
   (A)
   In general
   The eligible basis of an
   existing building
   is—
   (i)
   in the case of a building which meets the requirements of subparagraph (B), its adjusted basis as of the close of the 1st taxable year of the
   credit period
   , and
   (ii)
   zero in any other case.
   (B)
   Requirements
   A building meets the requirements of this subparagraph if—
   (i)
   the building is acquired by purchase (as defined in
   section 179(d)(2)
   ),
   (ii)
   there is a period of at least 10 years between the date of its acquisition by the taxpayer and the date the building was last placed in service,
   (iii)
   the building was not previously placed in service by the taxpayer or by any person who was a related person with respect to the taxpayer as of the time previously placed in service, and
   (iv)
   except as provided in subsection (f)(5), a credit is allowable under subsection (a) by reason of subsection (e) with respect to the building.
   (C)
   Adjusted basis
   For purposes of subparagraph (A), the adjusted basis of any building shall not include so much of the basis of such building as is determined by reference to the basis of other property held at any time by the person acquiring the building.
   (D)
   Special rules for subparagraph (B)
   (i)
   Special rules for certain transfers
   For purposes of determining under subparagraph (B)(ii) when a building was last placed in service, there shall not be taken into account any placement in service—
   (I)
   in connection with the acquisition of the building in a transaction in which the basis of the building in the hands of the person acquiring it is determined in whole or in part by reference to the adjusted basis of such building in the hands of the person from whom acquired,
   (II)
   by a person whose basis in such building is determined under section 1014(a) (relating to property acquired from a decedent),
   (III)
   by any governmental unit or
   qualified nonprofit organization
   (as defined in subsection (h)(5)) if the requirements of subparagraph (B)(ii) are met with respect to the placement in service by such unit or organization and all the income from such property is exempt from Federal income taxation,
   (IV)
   by any person who acquired such building by foreclosure (or by instrument in lieu of foreclosure) of any purchase-money security interest held by such person if the requirements of subparagraph (B)(ii) are met with respect to the placement in service by such person and such building is resold within 12 months after the date such building is placed in service by such person after such foreclosure, or
   (V)
   of a single-family residence by any individual who owned and used such residence for no other purpose than as his principal residence.
   (ii)
   Related person
   For purposes of subparagraph (B)(iii), a person (hereinafter in this subclause referred to as the “related person”) is related to any person if the related person bears a relationship to such person specified in
   section 267(b)
   or 707(b)(1), or the related person and such person are engaged in trades or businesses under common control (within the meaning of subsections (a) and (b) of section 52).
   (3)
   Eligible basis reduced where disproportionate standards for units
   (A)
   In general
   Except as provided in subparagraph (B), the eligible basis of any building shall be reduced by an amount equal to the portion of the adjusted basis of the building which is attributable to residential rental units in the building which are not
   low-income units
   and which are above the average quality standard of the
   low-income units
   in the building.
   (B)
   Exception where taxpayer elects to exclude excess costs
   (i)
   In general
   Subparagraph (A) shall not apply with respect to a residential rental unit in a building which is not a
   low-income unit
   if—
   (I)
   the excess described in clause (ii) with respect to such unit is not greater than 15 percent of the cost described in clause (ii)(II), and
   (II)
   the taxpayer elects to exclude from the eligible basis of such building the excess described in clause (ii) with respect to such unit.
   (ii)
   Excess
   The excess described in this clause with respect to any unit is the excess of—
   (I)
   the cost of such unit, over
   (II)
   the amount which would be the cost of such unit if the average cost per square foot of
   low-income units
   in the building were substituted for the cost per square foot of such unit.
   The Secretary may by regulation provide for the determination of the excess under this clause on a basis other than square foot costs.
   (4)
   Special rules relating to determination of adjusted basis
   For purposes of this subsection—
   (A)
   In general
   Except as provided in subparagraphs (B) and (C), the adjusted basis of any building shall be determined without regard to the adjusted basis of any property which is not residential rental property.
   (B)
   Basis of property in common areas, etc., included
   The adjusted basis of any building shall be determined by taking into account the adjusted basis of property (of a character subject to the allowance for depreciation) used in common areas or provided as comparable amenities to all residential rental units in such building.
   (C)
   Inclusion of basis of property used to provide services for certain nontenants
   (i)
   In general
   The adjusted basis of any building located in a
   qualified census tract
   (as defined in paragraph (5)(B)(ii)) shall be determined by taking into account the adjusted basis of property (of a character subject to the allowance for depreciation and not otherwise taken into account) used throughout the taxable year in providing any
   community service facility
   .
   (ii)
   Limitation
   The increase in the adjusted basis of any building which is taken into account by reason of clause (i) shall not exceed the sum of—
   (I)
   25 percent of so much of the eligible basis of the
   qualified low-income housing project
   of which it is a part as does not exceed $15,000,000, plus
   (II)
   10 percent of so much of the eligible basis of such project as is not taken into account under subclause (I).
   For purposes of the preceding sentence, all community service facilities which are part of the same
   qualified low-income housing project
   shall be treated as one facility.
   (iii)
   Community service facility
   For purposes of this subparagraph, the term “
   community service facility
   ” means any facility designed to serve primarily individuals whose income is 60 percent or less of area median income (within the meaning of subsection (g)(1)(B)).
   (D)
   No reduction for depreciation
   The adjusted basis of any building shall be determined without regard to paragraphs (2) and (3) of section 1016(a).
   (5)
   Special rules for determining eligible basis
   (A)
   Federal grants not taken into account in determining eligible basis
   The eligible basis of a building shall not include any costs financed with the proceeds of a federally funded grant.
   (B)
   Increase in credit for buildings in high cost areas
   (i)
   In general
   In the case of any building located in a
   qualified census tract
   or difficult development area which is designated for purposes of this subparagraph—
   (I)
   in the case of a
   new building
   , the eligible basis of such building shall be 130 percent of such basis determined without regard to this subparagraph, and
   (II)
   in the case of an
   existing building
   , the
   rehabilitation expenditures
   taken into account under subsection (e) shall be 130 percent of such expenditures determined without regard to this subparagraph.
   (ii)
   Qualified census tract
   (I)
   In general
   The term “
   qualified census tract
   ” means any census tract which is designated by the Secretary of Housing and Urban Development and, for the most recent year for which census data are available on household income in such tract, either in which 50 percent or more of the households have an income which is less than 60 percent of the area median gross income for such year or which has a poverty rate of at least 25 percent. If the Secretary of Housing and Urban Development determines that sufficient data for any period are not available to apply this clause on the basis of census tracts, such Secretary shall apply this clause for such period on the basis of enumeration districts.
   (II)
   Limit on MSA’s designated
   The portion of a
   metropolitan statistical area
   which may be designated for purposes of this subparagraph shall not exceed an area having 20 percent of the population of such
   metropolitan statistical area
   .
   (III)
   Determination of areas
   For purposes of this clause, each
   metropolitan statistical area
   shall be treated as a separate area and all
   nonmetropolitan areas
   in a
   State
   shall be treated as 1 area.
   (iii)
   Difficult development areas
   (I)
   In general
   The term “
   difficult development areas
   ” means any area designated by the Secretary of Housing and Urban Development as an area which has high construction, land, and utility costs relative to area median gross income.
   (II)
   Limit on areas designated
   The portions of
   metropolitan statistical areas
   which may be designated for purposes of this subparagraph shall not exceed an aggregate area having 20 percent of the population of such
   metropolitan statistical areas
   . A comparable rule shall apply to
   nonmetropolitan areas.
   (iv)
   Special rules and definitions
   For purposes of this subparagraph—
   (I)
   population shall be determined on the basis of the most recent decennial census for which data are available,
   (II)
   area median gross income shall be determined in accordance with subsection (g)(4),
   (III)
   the term “
   metropolitan statistical area
   ” has the same meaning as when used in section 143(k)(2)(B), and
   (IV)
   the term “
   nonmetropolitan area
   ” means any county (or portion thereof) which is not within a
   metropolitan statistical area
   .
   (v)
   Buildings designated by State housing credit agency
   Any building which is designated by the
   State
   housing credit agency
   as requiring the increase in credit under this subparagraph in order for such building to be financially feasible as part of a
   qualified low-income housing project
   shall be treated for purposes of this subparagraph as located in a difficult development area which is designated for purposes of this subparagraph. The preceding sentence shall not apply to any building if paragraph (1) of subsection (h) does not apply to any portion of the eligible basis of such building by reason of paragraph (4) of such subsection.
   (6)
   Credit allowable for certain buildings acquired during 10-year period described in paragraph (2)(B)(ii)
   (A)
   In general
   Paragraph (2)(B)(ii) shall not apply to any federally- or
   State-assisted building
   .
   (B)
   Buildings acquired from insured depository institutions in default
   On application by the taxpayer, the Secretary may waive paragraph (2)(B)(ii) with respect to any building acquired from an insured depository institution in default (as defined in section 3 of the
   Federal Deposit Insurance Act
   ) or from a receiver or conservator of such an institution.
   (C)
   Federally- or State-assisted building
   For purposes of this paragraph—
   (i)
   Federally-assisted building
   The term “
   federally-assisted building
   ” means any building which is substantially assisted, financed, or operated under section 8 of the
   United States Housing Act of 1937
   , section 221(d)(3), 221(d)(4), or 236 of the
   National Housing Act
   , section 515 of the
   Housing Act of 1949
   , or any other housing program administered by the
   Department of Housing and Urban Development
   or by the Rural Housing Service of the
   Department of Agriculture
   .
   (ii)
   State-assisted building
   The term “
   State-assisted building
   ” means any building which is substantially assisted, financed, or operated under any
   State
   law similar in purposes to any of the laws referred to in clause (i).
   (7)
   Acquisition of building before end of prior compliance period
   (A)
   In general
   Under regulations prescribed by the Secretary, in the case of a building described in subparagraph (B) (or interest therein) which is acquired by the taxpayer—
   (i)
   paragraph (2)(B) shall not apply, but
   (ii)
   the credit allowable by reason of subsection (a) to the taxpayer for any period after such acquisition shall be equal to the amount of credit which would have been allowable under subsection (a) for such period to the prior owner referred to in subparagraph (B) had such owner not disposed of the building.
   (B)
   Description of building
   A building is described in this subparagraph if—
   (i)
   a credit was allowed by reason of subsection (a) to any prior owner of such building, and
   (ii)
   the taxpayer acquired such building before the end of the
   compliance period
   for such building with respect to such prior owner (determined without regard to any
   disposition
   by such prior owner).
   (e)
   Rehabilitation expenditures treated as separate new building
   (1)
   In general
   Rehabilitation expenditures paid or incurred by the taxpayer with respect to any building shall be treated for purposes of this section as a separate
   new building
   .
   (2)
   Rehabilitation expenditures
   For purposes of paragraph (1)—
   (A)
   In general
   The term “
   rehabilitation expenditures
   ” means amounts chargeable to capital account and incurred for property (or additions or improvements to property) of a character subject to the allowance for depreciation in connection with the rehabilitation of a building.
   (B)
   Cost of acquisition, etc., not included
   Such term does not include the cost of acquiring any building (or interest therein) or any amount not permitted to be taken into account under paragraph (3) or (4) of subsection (d).
   (3)
   Minimum expenditures to qualify
   (A)
   In general
   Paragraph (1) shall apply to
   rehabilitation expenditures
   with respect to any building only if—
   (i)
   the expenditures are allocable to 1 or more
   low-income units
   or substantially benefit such units, and
   (ii)
   the amount of such expenditures during any 24-month period meets the requirements of whichever of the following subclauses requires the greater amount of such expenditures:
   (I)
   The requirement of this subclause is met if such amount is not less than 20 percent of the adjusted basis of the building (determined as of the 1st day of such period and without regard to paragraphs (2) and (3) of
   section 1016(a)
   ).
   (II)
   The requirement of this subclause is met if the qualified basis attributable to such amount, when divided by the number of
   low-income units
   in the building, is $6,000 or more.
   (B)
   Exception from 10 percent rehabilitation
   In the case of a building acquired by the taxpayer from a governmental unit, at the election of the taxpayer, subparagraph (A)(ii)(I) shall not apply and the credit under this section for such
   rehabilitation expenditures
   shall be determined using the percentage applicable under subsection (b)(2)(B)(ii).
   (C)
   Date of determination
   The determination under subparagraph (A) shall be made as of the close of the 1st taxable year in the
   credit period
   with respect to such expenditures.
   (D)
   Inflation adjustment
   In the case of any expenditures which are treated under paragraph (4) as placed in service during any calendar year after 2009, the $6,000 amount in subparagraph (A)(ii)(II) shall be increased by an amount equal to—
   (i)
   such dollar amount, multiplied by
   (ii)
   the cost-of-living adjustment determined under section 1(f)(3) for such calendar year by substituting “calendar year 2008” for “calendar year 2016” in subparagraph (A)(ii) thereof.
   Any increase under the preceding sentence which is not a multiple of $100 shall be rounded to the nearest multiple of $100.
   (4)
   Special rules
   For purposes of applying this section with respect to expenditures which are treated as a separate building by reason of this subsection—
   (A)
   such expenditures shall be treated as placed in service at the close of the 24-month period referred to in paragraph (3)(A), and
   (B)
   the
   applicable fraction
   under subsection (c)(1) shall be the
   applicable fraction
   for the building (without regard to paragraph (1)) with respect to which the expenditures were incurred.
   Nothing in subsection (d)(2) shall prevent a credit from being allowed by reason of this subsection.
   (5)
   No double counting
   Rehabilitation expenditures may, at the election of the taxpayer, be taken into account under this subsection or subsection (d)(2)(A)(i) but not under both such subsections.
   (6)
   Regulations to apply subsection with respect to group of units in building
   The Secretary may prescribe regulations, consistent with the purposes of this subsection, treating a group of units with respect to which
   rehabilitation expenditures
   are incurred as a separate
   new building
   .
   (f)
   Definition and special rules relating to credit period
   (1)
   Credit period defined
   For purposes of this section, the term “
   credit period
   ” means, with respect to any building, the period of 10 taxable years beginning with—
   (A)
   the taxable year in which the building is placed in service, or
   (B)
   at the election of the taxpayer, the succeeding taxable year,
   but only if the building is a
   qualified low-income building
   as of the close of the 1st year of such period. The election under subparagraph (B), once made, shall be irrevocable.
   (2)
   Special rule for 1st year of credit period
   (A)
   In general
   The credit allowable under subsection (a) with respect to any building for the 1st taxable year of the
   credit period
   shall be determined by substituting for the
   applicable fraction
   under subsection (c)(1) the fraction—
   (i)
   the numerator of which is the sum of the
   applicable fractions
   determined under subsection (c)(1) as of the close of each full month of such year during which such building was in service, and
   (ii)
   the denominator of which is 12.
   (B)
   Disallowed 1st year credit allowed in 11th year
   Any reduction by reason of subparagraph (A) in the credit allowable (without regard to subparagraph (A)) for the 1st taxable year of the
   credit period
   shall be allowable under subsection (a) for the 1st taxable year following the
   credit period
   .
   (3)
   Determination of applicable percentage with respect to increases in qualified basis after 1st year of credit period
   (A)
   In general
   In the case of any building which was a
   qualified low-income building
   as of the close of the 1st year of the
   credit period,
   if—
   (i)
   as of the close of any taxable year in the
   compliance period
   (after the 1st year of the
   credit period)
   the qualified basis of such building exceeds
   (ii)
   the qualified basis of such building as of the close of the 1st year of the
   credit period

-- [Content truncated - key provisions above]


-/
-- TODO: Add type definitions
-- TODO: Add main functions
-- TODO: Add theorems to prove