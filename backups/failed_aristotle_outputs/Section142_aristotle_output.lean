/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8921cc86-2cc0-46cd-8f3a-4d0caf497253

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
# IRC Section 142 - Exempt facility bond

This file formalizes IRC §142 (Exempt facility bond).

## References
- [26 USC §142](https://www.law.cornell.edu/uscode/text/26/142)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 142 - Exempt facility bond
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   General rule
   For purposes of this part, the term “
   exempt facility bond
   ” means any
   bond
   issued as part of an issue 95 percent or more of the
   net proceeds
   of which are to be used to provide—
   (1)
   airports and
   spaceports
   ,
   (2)
   docks and wharves,
   (3)
   mass commuting facilities,
   (4)
   facilities for the furnishing of water
   ,
   (5)
   sewage facilities,
   (6)
   solid waste disposal facilities,
   (7)
   qualified residential rental projects
   ,
   (8)
   facilities for the local furnishing of electric energy or gas,
   (9)
   local district heating or cooling facilities,
   (10)
   qualified hazardous waste facilities,
   (11)
   high-speed intercity rail facilities
   ,
   (12)
   environmental enhancements of hydroelectric generating facilities
   ,
   (13)
   qualified public educational facilities,
   (14)
   qualified green building and sustainable design projects
   ,
   (15)
   qualified highway or surface freight transfer facilities
   ,
   (16)
   qualified broadband projects
   , or
   (17)
   qualified carbon dioxide capture facilities.
   (b)
   Special exempt facility bond rules
   For purposes of subsection (a)—
   (1)
   Certain facilities must be governmentally owned
   (A)
   In general
   A facility shall be treated as described in paragraph (1), (2), (3), or (12) of subsection (a) only if all of the property to be financed by the
   net proceeds
   of the issue is to be owned by a governmental unit.
   (B)
   Safe harbor for leases and management contracts
   For purposes of subparagraph (A), property leased by a governmental unit shall be treated as owned by such governmental unit if—
   (i)
   the lessee makes an irrevocable election (binding on the lessee and all successors in interest under the lease) not to claim depreciation or an investment credit with respect to such property,
   (ii)
   the lease term (as defined in section 168(i)(3)) is not more than 80 percent of the reasonably expected economic life of the property (as determined under section 147(b)), and
   (iii)
   the lessee has no option to purchase the property other than at fair market value (as of the time such option is exercised).
   Rules similar to the rules of the preceding sentence shall apply to management contracts and similar types of operating agreements.
   (C)
   Special rule for spaceport ground leases
   For purposes of subparagraph (A),
   spaceport
   property located on land leased by a governmental unit from the United States shall not fail to be treated as owned by a governmental unit if the requirements of this paragraph are met by the lease and any subleases of the property.
   (2)
   Limitation on office space
   An office shall not be treated as described in a paragraph of subsection (a) unless—
   (A)
   the office is located on the premises of a facility described in such a paragraph, and
   (B)
   not more than a de minimis amount of the functions to be performed at such office is not directly related to the day-to-day operations at such facility.
   (c)
   Airports, spaceports, docks and wharves, mass commuting facilities and high-speed intercity rail facilities
   For purposes of subsection (a)—
   (1)
   Storage and training facilities
   Storage or training facilities directly related to a facility described in paragraph (1), (2), (3) or (11) of subsection (a) shall be treated as described in the paragraph in which such facility is described.
   (2)
   Exception for certain private facilities
   Property shall not be treated as described in paragraph (1), (2), (3) or (11) of subsection (a) if such property is described in any of the following subparagraphs and is to be used for any private business use (as defined in
   section 141(b)(6)
   ).
   (A)
   Any lodging facility.
   (B)
   Any retail facility (including food and beverage facilities) in excess of a size necessary to serve passengers and employees at the exempt facility.
   (C)
   Any retail facility (other than parking) for passengers or the general public located outside the exempt facility terminal.
   (D)
   Any office building for individuals who are not employees of a governmental unit or of the operating authority for the exempt facility.
   (E)
   Any industrial park or manufacturing facility.
   (d)
   Qualified residential rental project
   For purposes of this section—
   (1)
   In general
   The term “
   qualified residential rental project
   ” means any project for residential rental property if, at all times during the
   qualified project period,
   such project meets the requirements of subparagraph (A) or (B), whichever is elected by the issuer at the time of the issuance of the issue with respect to such project:
   (A)
   20–50 test
   The project meets the requirements of this subparagraph if 20 percent or more of the residential units in such project are occupied by individuals whose income is 50 percent or less of area median gross income.
   (B)
   40–60 test
   The project meets the requirements of this subparagraph if 40 percent or more of the residential units in such project are occupied by individuals whose income is 60 percent or less of area median gross income.
   For purposes of this paragraph, any property shall not be treated as failing to be residential rental property merely because part of the building in which such property is located is used for purposes other than residential rental purposes.
   (2)
   Definitions and special rules
   For purposes of this subsection—
   (A)
   Qualified project period
   The term “
   qualified project period
   ” means the period beginning on the 1st day on which 10 percent of the residential units in the project are occupied and ending on the latest of—
   (i)
   the date which is 15 years after the date on which 50 percent of the residential units in the project are occupied,
   (ii)
   the 1st day on which no
   tax-exempt
   private activity bond
   issued with respect to the project is outstanding, or
   (iii)
   the date on which any assistance provided with respect to the project under section 8 of the
   United States Housing Act of 1937
   terminates.
   (B)
   Income of individuals; area median gross income
   (i)
   In general
   The income of individuals and area median gross income shall be determined by the Secretary in a manner consistent with determinations of lower income families and area median gross income under section 8 of the
   United States Housing Act of 1937
   (or, if such program is terminated, under such program as in effect immediately before such termination). Determinations under the preceding sentence shall include adjustments for family size. Subsections (g) and (h) of
   section 7872
   shall not apply in determining the income of individuals under this subparagraph.
   (ii)
   Special rule relating to basic housing allowances
   For purposes of determining income under this subparagraph, payments under
   section 403 of title 37
   , United States Code, as a basic pay allowance for housing shall be disregarded with respect to any
   qualified building.
   (iii)
   Qualified building
   For purposes of clause (ii), the term “
   qualified building
   ” means any building located—
   (I)
   in any county in which is located a
   qualified military installation
   to which the number of members of the Armed Forces of the United States assigned to units based out of such
   qualified military installation
   , as of
   June 1, 2008
   , has increased by not less than 20 percent, as compared to such number on
   December 31, 2005
   , or
   (II)
   in any county adjacent to a county described in subclause (I).
   (iv)
   Qualified military installation
   For purposes of clause (iii), the term “
   qualified military installation
   ” means any military installation or facility the number of members of the Armed Forces of the United States assigned to which, as of
   June 1, 2008
   , is not less than 1,000.
   (C)
   Students
   Rules similar to the rules of
   section 42(i)(3)(D)
   shall apply for purposes of this subsection.
   (D)
   Single-room occupancy units
   A unit shall not fail to be treated as a residential unit merely because such unit is a single-room occupancy unit (within the meaning of
   section 42
   ).
   (E)
   Hold harmless for reductions in area median gross income
   (i)
   In general
   Any determination of area median gross income under subparagraph (B) with respect to any project for any calendar year after 2008 shall not be less than the area median gross income determined under such subparagraph with respect to such project for the calendar year preceding the calendar year for which such determination is made.
   (ii)
   Special rule for certain census changes
   In the case of a
   HUD hold harmless impacted project
   , the area median gross income with respect to such project for any calendar year after 2008 (hereafter in this clause referred to as the current calendar year) shall be the greater of the amount determined without regard to this clause or the sum of—
   (I)
   the area median gross income determined under the
   HUD hold harmless policy
   with respect to such project for calendar year 2008, plus
   (II)
   any increase in the area median gross income determined under subparagraph (B) (determined without regard to the
   HUD hold harmless policy
   and this subparagraph) with respect to such project for the current calendar year over the area median gross income (as so determined) with respect to such project for calendar year 2008.
   (iii)
   HUD hold harmless policy
   The term “
   HUD hold harmless policy
   ” means the regulations under which a policy similar to the rules of clause (i) applied to prevent a change in the method of determining area median gross income from resulting in a reduction in the area median gross income determined with respect to certain projects in calendar years 2007 and 2008.
   (iv)
   HUD hold harmless impacted project
   The term “
   HUD hold harmless impacted project
   ” means any project with respect to which area median gross income was determined under subparagraph (B) for calendar year 2007 or 2008 if such determination would have been less but for the
   HUD hold harmless policy.
   (3)
   Current income determinations
   For purposes of this subsection—
   (A)
   In general
   The determination of whether the income of a resident of a unit in a project exceeds the
   applicable income limit
   shall be made at least annually on the basis of the current income of the resident. The preceding sentence shall not apply with respect to any project for any year if during such year no residential unit in the project is occupied by a new resident whose income exceeds the
   applicable income limit
   .
   (B)
   Continuing resident’s income may increase above the applicable limit
   If the income of a resident of a unit in a project did not exceed the
   applicable income limit
   upon commencement of such resident’s occupancy of such unit (or as of any prior determination under subparagraph (A)), the income of such resident shall be treated as continuing to not exceed the
   applicable income limit
   . The preceding sentence shall cease to apply to any resident whose income as of the most recent determination under subparagraph (A) exceeds 140 percent of the
   applicable income limit
   if after such determination, but before the next determination, any residential unit of comparable or smaller size in the same project is occupied by a new resident whose income exceeds the
   applicable income limit
   .
   (C)
   Exception for projects with respect to which affordable housing credit is allowed
   In the case of a project with respect to which credit is allowed under section 42, the second sentence of subparagraph (B) shall be applied by substituting “building (within the meaning of
   section 42
   )” for “project”.
   (4)
   Special rule in case of deep rent skewing
   (A)
   In general
   In the case of any project described in subparagraph (B), the 2d sentence of subparagraph (B) of paragraph (3) shall be applied by substituting—
   (i)
   “170 percent” for “140 percent”, and
   (ii)
   “any
   low-income unit
   in the same project is occupied by a new resident whose income exceeds 40 percent of area median gross income” for “any residential unit of comparable or smaller size in the same project is occupied by a new resident whose income exceeds the
   applicable income limit
   ”.
   (B)
   Deep rent skewed project
   A project is described in this subparagraph if the owner of the project elects to have this paragraph apply and, at all times during the
   qualified project period
   , such project meets the requirements of clauses (i), (ii), and (iii):
   (i)
   The project meets the requirements of this clause if 15 percent or more of the
   low-income units
   in the project are occupied by individuals whose income is 40 percent or less of area median gross income.
   (ii)
   The project meets the requirements of this clause if the
   gross rent
   with respect to each
   low-income unit
   in the project does not exceed 30 percent of the
   applicable income limit
   which applies to individuals occupying the unit.
   (iii)
   The project meets the requirements of this clause if the
   gross rent
   with respect to each
   low-income unit
   in the project does not exceed ½ of the average
   gross rent
   with respect to units of comparable size which are not occupied by individuals who meet the
   applicable income limit
   .
   (C)
   Definitions applicable to subparagraph (B)
   For purposes of subparagraph (B)—
   (i)
   Low-income unit
   The term “
   low-income unit
   ” means any unit which is required to be occupied by individuals who meet the
   applicable income limit
   .
   (ii)
   Gross rent
   The term “
   gross rent
   ” includes—
   (I)
   any payment under section 8 of the
   United States Housing Act of 1937
   , and
   (II)
   any utility allowance determined by the Secretary after taking into account such determinations under such section 8.
   (5)
   Applicable income limit
   For purposes of paragraphs (3) and (4), the term “
   applicable income limit
   ” means—
   (A)
   the limitation under subparagraph (A) or (B) of paragraph (1) which applies to the project, or
   (B)
   in the case of a unit to which paragraph (4)(B)(i) applies, the limitation which applies to such unit.
   (6)
   Special rule for certain high cost housing area
   In the case of a project located in a city having 5 boroughs and a population in excess of 5,000,000, subparagraph (B) of paragraph (1) shall be applied by substituting “25 percent” for “40 percent”.
   (7)
   Certification to Secretary
   The operator of any project with respect to which an election was made under this subsection shall submit to the Secretary (at such time and in such manner as the Secretary shall prescribe) an annual certification as to whether such project continues to meet the requirements of this subsection. Any failure to comply with the provisions of the preceding sentence shall not affect the
   tax-exempt
   status of any
   bond
   but shall subject the operator to penalty, as provided in section 6652(j).
   (e)
   Facilities for the furnishing of water
   For purposes of subsection (a)(4), the term “
   facilities for the furnishing of water
   ” means any facility for the furnishing of water if—
   (1)
   the water is or will be made available to members of the general public (including electric utility, industrial, agricultural, or commercial users), and
   (2)
   either the facility is operated by a governmental unit or the rates for the furnishing or sale of the water have been established or approved by a State or political subdivision thereof, by an agency or instrumentality of the United States, or by a public service or public utility commission or other similar body of any State or political subdivision thereof.
   (f)
   Local furnishing of electric energy or gas
   For purposes of subsection (a)(8)—
   (1)
   In general
   The local furnishing of electric energy or gas from a facility shall only include furnishing solely within the area consisting of—
   (A)
   a city and 1 contiguous county, or
   (B)
   2 contiguous counties.
   (2)
   Treatment of certain electric energy transmitted outside local area
   (A)
   In general
   A facility shall not be treated as failing to meet the local furnishing requirement of subsection (a)(8) by reason of electricity transmitted pursuant to an order of the
   Federal Energy Regulatory Commission
   under section 211 or 213 of the
   Federal Power Act
   (as in effect on the date of the enactment of this paragraph) if the portion of the cost of the facility financed with
   tax-exempt
   bonds is not greater than the portion of the cost of the facility which is allocable to the local furnishing of electric energy (determined without regard to this paragraph).
   (B)
   Special rule for existing facilities
   In the case of a facility financed with
   bonds
   issued before the date of an order referred to in subparagraph (A) which would (but for this subparagraph) cease to be
   tax-exempt
   by reason of subparagraph (A), such
   bonds
   shall not cease to be
   tax-exempt
   bonds
   (and
   section 150(b)(4)
   shall not apply) if, to the extent necessary to comply with subparagraph (A)—
   (i)
   an escrow to pay principal of, premium (if any), and interest on the
   bonds
   is established within a reasonable period after the date such order becomes final, and
   (ii)
   bonds
   are redeemed not later than the earliest date on which such
   bonds
   may be redeemed.
   (3)
   Termination of future financing
   For purposes of this section, no
   bond
   may be issued as part of an issue described in subsection (a)(8) with respect to a facility for the local furnishing of electric energy or gas on or after the date of the enactment of this paragraph unless—
   (A)
   the facility will—
   (i)
   be used by a
   person
   who is engaged in the local furnishing of that energy source on
   January 1, 1997
   , and
   (ii)
   be used to provide service within the area served by such
   person
   on
   January 1, 1997
   (or within a county or city any portion of which is within such area), or
   (B)
   the facility will be used by a successor in interest to such
   person
   for the same use and within the same service area as described in subparagraph (A).
   (4)
   Election to terminate tax-exempt bond financing by certain furnishers
   (A)
   In general
   In the case of a facility financed with
   bonds
   issued before the date of the enactment of this paragraph which would cease to be
   tax-exempt
   by reason of the failure to meet the local furnishing requirement of subsection (a)(8) as a result of a service area expansion, such
   bonds
   shall not cease to be
   tax-exempt
   bonds
   (and
   section 150(b)(4)
   shall not apply) if the
   person
   engaged in such local furnishing by such facility makes an election described in subparagraph (B).
   (B)
   Election
   An election is described in this subparagraph if it is an election made in such manner as the Secretary prescribes, and such
   person
   (or its predecessor in interest) agrees that—
   (i)
   such election is made with respect to all facilities for the local furnishing of electric energy or gas, or both, by such
   person
   ,
   (ii)
   no
   bond
   exempt from tax under section 103 and described in subsection (a)(8) may be issued on or after the date of the enactment of this paragraph with respect to all such facilities of such
   person
   ,
   (iii)
   any expansion of the service area—
   (I)
   is not financed with the proceeds of any
   exempt facility bond
   described in subsection (a)(8), and
   (II)
   is not treated as a nonqualifying use under the rules of paragraph (2), and
   (iv)
   all outstanding
   bonds
   used to finance the facilities for such
   person
   are redeemed not later than 6 months after the later of—
   (I)
   the earliest date on which such
   bonds
   may be redeemed, or
   (II)
   the date of the election.
   (C)
   Related persons
   For purposes of this paragraph, the term “
   person
   ” includes a group of related
   persons
   (within the meaning of
   section 144(a)(3)
   ) which includes such
   person.
   (g)
   Local district heating or cooling facility
   (1)
   In general
   For purposes of subsection (a)(9), the term “
   local district heating or cooling facility
   ” means property used as an integral part of a
   local district heating or cooling system
   .
   (2)
   Local district heating or cooling system
   (A)
   In general
   For purposes of paragraph (1), the term “
   local district heating or cooling system
   ” means any local system consisting of a pipeline or network (which may be connected to a heating or cooling source) providing hot water, chilled water, or steam to 2 or more users for—
   (i)
   residential, commercial, or industrial heating or cooling, or
   (ii)
   process steam.
   (B)
   Local system
   For purposes of this paragraph, a local system includes facilities furnishing heating and cooling to an area consisting of a city and 1 contiguous county.
   (h)
   Qualified hazardous waste facilities
   For purposes of subsection (a)(10), the term “
   qualified hazardous waste facility
   ” means any facility for the disposal of hazardous waste by incineration or entombment but only if—
   (1)
   the facility is subject to final permit requirements under subtitle C of title II of the
   Solid Waste Disposal Act
   (as in effect on the date of the enactment of the
   Tax Reform Act of 1986
   ), and
   (2)
   the portion of such facility which is to be provided by the issue does not exceed the portion of the facility which is to be used by
   persons
   other than—
   (A)
   the owner or operator of such facility, and
   (B)
   any related
   person
   (within the meaning of
   section 144(a)(3)
   ) to such owner or operator.
   (i)
   High-speed intercity rail facilities
   (1)
   In general
   For purposes of subsection (a)(11), the term “
   high-speed intercity rail facilities
   ” means any facility (not including rolling stock) for the fixed guideway rail transportation of passengers and their baggage between metropolitan statistical areas (within the meaning of section 143(k)(2)(B)) using vehicles that are reasonably expected to be capable of attaining a maximum speed in excess of 150 miles per hour between scheduled stops, but only if such facility will be made available to members of the general public as passengers.
   (2)
   Election by nongovernmental owners
   A facility shall be treated as described in subsection (a)(11) only if any owner of such facility which is not a governmental unit irrevocably elects not to claim—
   (A)
   any deduction under
   section 167
   or 168, and
   (B)
   any credit under this subtitle,
   with respect to the property to be financed by the
   net proceeds
   of the issue.
   (3)
   Use of proceeds
   A
   bond
   issued as part of an issue described in subsection (a)(11) shall not be considered an
   exempt facility bond
   unless any proceeds not used within a 3-year period of the date of the issuance of such
   bond
   are used (not later than 6 months after the close of such period) to redeem
   bonds
   which are part of such issue.
   (j)
   Environmental enhancements of hydroelectric generating facilities
   (1)
   In general
   For purposes of subsection (a)(12), the term “
   environmental enhancements of hydroelectric generating facilities
   ” means property—
   (A)
   the use of which is related to a federally licensed hydroelectric generating facility owned and operated by a governmental unit, and
   (B)
   which—
   (i)
   protects or promotes fisheries or other wildlife
   resources
   , including any fish by-pass facility, fish hatchery, or fisheries enhancement facility, or
   (ii)
   is a recreational facility or other improvement required by the terms and conditions of any Federal licensing permit for the operation of such generating facility.
   (2)
   Use of proceeds
   A
   bond
   issued as part of an issue described in subsection (a)(12) shall not be considered an
   exempt facility bond
   unless at least 80 percent of the
   net proceeds
   of the issue of which it is a part are used to finance property described in paragraph (1)(B)(i).
   (k)
   Qualified public educational facilities
   (1)
   In general
   For purposes of subsection (a)(13), the term “
   qualified public educational facility
   ” means any
   school facility
   which is—
   (A)
   part of a public
   elementary school

-- [Content truncated - key provisions above]

-- TODO: Add type definitions
-- TODO: Add main functions
-- TODO: Add theorems to prove