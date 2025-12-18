/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 037e83fa-dd3e-4cc9-bf82-9fc312ef1553

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
# IRC Section 1016 - Adjustments to basis

This file formalizes IRC §1016 (Adjustments to basis).

## References
- [26 USC §1016](https://www.law.cornell.edu/uscode/text/26/1016)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1016 - Adjustments to basis
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   Proper adjustment in respect of the property shall in all cases be made—
   (1)
   for expenditures, receipts, losses, or other items, properly chargeable to capital account, but no such adjustment shall be made—
   (A)
   for—
   (i)
   taxes or other carrying charges described in section 266; or
   (ii)
   expenditures described in section 173 (relating to circulation expenditures),
   for which deductions have been taken by the taxpayer in determining taxable income for the taxable year or prior taxable years; or
   (B)
   for mortality, expense, or other reasonable charges incurred under an annuity or life insurance contract;
   (2)
   in respect of any period since
   February 28, 1913
   , for exhaustion, wear and tear, obsolescence, amortization, and depletion, to the extent of the amount—
   (A)
   allowed as deductions in computing taxable income under this subtitle or prior income tax laws, and
   (B)
   resulting (by reason of the deductions so allowed) in a reduction for any taxable year of the taxpayer’s taxes under this subtitle (other than chapter 2, relating to tax on self-employment income), or prior income, war-profits, or excess-profits tax laws,
   but not less than the amount allowable under this subtitle or prior income tax laws. Where no method has been adopted under section 167 (relating to depreciation deduction), the amount allowable shall be determined under the straight line method. Subparagraph (B) of this paragraph shall not apply in respect of any period since
   February 28, 1913
   , and before
   January 1, 1952
   , unless an election has been made under section 1020 (as in effect before the date of the enactment of the
   Tax Reform Act of 1976
   ). Where for any taxable year before the taxable year 1932 the depletion allowance was based on discovery value or a percentage of income, then the adjustment for depletion for such year shall be based on the depletion which would have been allowable for such year if computed without reference to discovery value or a percentage of income;
   (3)
   in respect of any period—
   (A)
   before
   March 1, 1913
   ,
   (B)
   since
   February 28, 1913
   , during which such property was held by a person or an organization not subject to income taxation under this chapter or prior income tax laws,
   (C)
   since
   February 28, 1913
   , and before
   January 1, 1958
   , during which such property was held by a person subject to tax under part I of subchapter L (or the corresponding provisions of prior income tax laws), to the extent that paragraph (2) does not apply, and
   (D)
   since
   February 28, 1913
   , during which such property was held by a person subject to tax under part II of subchapter L as in effect prior to its repeal by the
   Tax Reform Act of 1986
   (or the corresponding provisions of prior income tax laws), to the extent that paragraph (2) does not apply,
   for exhaustion, wear and tear, obsolescence, amortization, and depletion, to the extent sustained;
   (4)
   in the case of stock (to the extent not provided for in the foregoing paragraphs) for the amount of distributions previously made which, under the law applicable to the year in which the distribution was made, either were tax-free or were applicable in reduction of basis (not including distributions made by a corporation which was classified as a personal service corporation under the provisions of the
   Revenue Act of 1918
   (
   40 Stat. 1057
   ), or the
   Revenue Act of 1921
   (
   42 Stat. 227
   ), out of its earnings or profits which were taxable in accordance with the provisions of section 218 of the
   Revenue Act of 1918
   or 1921);
   (5)
   in the case of any bond (as defined in section 171(d)) the interest on which is wholly exempt from the tax imposed by this subtitle, to the extent of the amortizable bond premium disallowable as a deduction pursuant to section 171(a)(2), and in the case of any other bond (as defined in section 171(d)) to the extent of the deductions allowable pursuant to section 171(a)(1) (or the amount applied to reduce interest payments under section 171(e)(2)) with respect thereto;
   (6)
   in the case of any municipal bond (as defined in
   section 75(b)
   ), to the extent provided in section 75(a)(2);
   (7)
   in the case of a residence the acquisition of which resulted, under section 1034 (as in effect on the day before the date of the enactment of the
   Taxpayer Relief Act of 1997
   ), in the nonrecognition of any part of the gain realized on the sale, exchange, or involuntary conversion of another residence, to the extent provided in section 1034(e) (as so in effect);
   (8)
   in the case of property pledged to the
   Commodity Credit Corporation
   , to the extent of the amount received as a loan from the
   Commodity Credit Corporation
   and treated by the taxpayer as income for the year in which received pursuant to section 77, and to the extent of any deficiency on such loan with respect to which the taxpayer has been relieved from liability;
   (9)
   for amounts allowed as deductions as deferred expenses under section 616(b) (relating to certain expenditures in the development of mines) and resulting in a reduction of the taxpayer’s taxes under this subtitle, but not less than the amounts allowable under such section for the taxable year and prior years;
   [(10)
   Repealed.
   Pub. L. 94–455, title XIX, § 1901(b)(21)(G)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1798
   ]
   (11)
   for deductions to the extent disallowed under section 268 (relating to sale of land with unharvested crops), notwithstanding the provisions of any other paragraph of this subsection;
   [(12)
   Repealed.
   Pub. L. 113–295, div. A, title II, § 221(a)(75)
   ,
   Dec. 19, 2014
   ,
   128 Stat. 4049
   ]
   [(13)
   Repealed.
   Pub. L. 108–357, title IV, § 413(c)(19)
   ,
   Oct. 22, 2004
   ,
   118 Stat. 1509
   ]
   (14)
   for amounts allowed as deductions under section 174 or 174A(c) and resulting in a reduction of the taxpayers’ taxes under this subtitle, but not less than the amounts allowable under such section for the taxable year and prior years;
   (15)
   for deductions to the extent disallowed under section 272 (relating to disposal of coal or domestic iron ore), notwithstanding the provisions of any other paragraph of this subsection;
   (16)
   in the case of any evidence of indebtedness referred to in section 811(b) (relating to amortization of premium and accrual of discount in the case of life insurance companies), to the extent of the adjustments required under section 811(b) (or the corresponding provisions of prior income tax laws) for the taxable year and all prior taxable years;
   (17)
   to the extent provided in
   section 1367
   in the case of stock of, and indebtedness owed to, shareholders of an S corporation;
   (18)
   to the extent provided in
   section 961
   in the case of stock in
   controlled foreign corporations
   (or foreign corporations which were
   controlled foreign corporations)
   and of property by reason of which a person is considered as owning such stock;
   (19)
   to the extent provided in section 50(c), in the case of expenditures with respect to which a credit has been allowed under section 38;
   (20)
   for amounts allowed as deductions under section 59(e) (relating to optional 10-year writeoff of certain tax preferences);
   (21)
   to the extent provided in section 1059 (relating to reduction in basis for extraordinary dividends);
   (22)
   in the case of qualified replacement property the acquisition of which resulted under section 1042 in the nonrecognition of any part of the gain realized on the sale or exchange of any property, to the extent provided in section 1042(d),
   [1]
   (23)
   in the case of property the acquisition of which resulted under section 1043, 1045, or 1397B in the nonrecognition of any part of the gain realized on the sale of other property, to the extent provided in section 1043(c), 1045(b)(3), or 1397B(b)(4), as the case may be,
   1
   [(24)
   Repealed.
   Pub. L. 113–295, div. A, title II, § 221(a)(34)(G)
   ,
   Dec. 19, 2014
   ,
   128 Stat. 4042
   ]
   [(25)
   Repealed.
   Pub. L. 113–295, div. A, title II, § 221(a)(2)(D)
   ,
   Dec. 19, 2014
   ,
   128 Stat. 4037
   ]
   (26)
   to the extent provided in sections 23(g) and 137(e),
   1
   [(27)
   Repealed.
   Pub. L. 115–141, div. U, title IV, § 401(d)(4)(B)(iv)
   ,
   Mar. 23, 2018
   ,
   132 Stat. 1209
   ]
   (28)
   in the case of a facility with respect to which a credit was allowed under section 45F, to the extent provided in section 45F(f)(1),
   1
   (29)
   in the case of railroad track with respect to which a credit was allowed under section 45G, to the extent provided in section 45G(e)(3),
   1
   (30)
   to the extent provided in section 179B(c),
   1
   (31)
   to the extent provided in section 179D(e),
   1
   (32)
   to the extent provided in section 45L(e), in the case of amounts with respect to which a credit has been allowed under section 45L,
   1
   (33)
   to the extent provided in section 25C(g), in the case of amounts with respect to which a credit has been allowed under section 25C,
   1
   (34)
   to the extent provided in section 25D(f), in the case of amounts with respect to which a credit has been allowed under section 25D,
   1
   (35)
   to the extent provided in section 30B(h)(4),
   1
   (36)
   to the extent provided in section 30C(e)(1),
   1
   (37)
   to the extent provided in section 30D(f)(1),
   1
   and
   (38)
   to the extent provided in subsections (b)(2) and (c) of section 1400Z–2.
   (b)
   Substituted basis
   Whenever it appears that the basis of property in the hands of the taxpayer is a substituted basis, then the adjustments provided in subsection (a) shall be made after first making in respect of such substituted basis proper adjustments of a similar nature in respect of the period during which the property was held by the transferor, donor, or grantor, or during which the other property was held by the person for whom the basis is to be determined. A similar rule shall be applied in the case of a series of substituted bases.
   (c)
   Increase in basis of property on which additional estate tax is imposed
   (1)
   Tax imposed with respect to entire interest
   If an additional estate tax is imposed under
   section 2032A(c)(1)
   with respect to any interest in property and the qualified heir makes an election under this subsection with respect to the imposition of such tax, the adjusted basis of such interest shall be increased by an amount equal to the excess of—
   (A)
   the fair market value of such interest on the date of the decedent’s death (or the alternate valuation date under section 2032, if the executor of the decedent’s estate elected the application of such section), over
   (B)
   the value of such interest determined under section 2032A(a).
   (2)
   Partial dispositions
   (A)
   In general
   In the case of any
   partial disposition
   for which an election under this subsection is made, the increase in basis under paragraph (1) shall be an amount—
   (i)
   which bears the same ratio to the increase which would be determined under paragraph (1) (without regard to this paragraph) with respect to the entire interest, as
   (ii)
   the amount of the tax imposed under
   section 2032A(c)(1)
   with respect to such
   disposition
   bears to the adjusted tax difference attributable to the entire interest (as determined under section 2032A(c)(2)(B)).
   (B)
   Partial disposition
   For purposes of subparagraph (A), the term “
   partial disposition
   ” means any
   disposition
   or cessation to which subsection (c)(2)(D), (h)(1)(B), or (i)(1)(B) of
   section 2032A
   applies.
   (3)
   Time adjustment made
   Any increase in basis under this subsection shall be deemed to have occurred immediately before the
   disposition
   or cessation resulting in the imposition of the tax under section 2032A(c)(1).
   (4)
   Special rule in the case of substituted property
   If the tax under
   section 2032A(c)(1)
   is imposed with respect to qualified replacement property (as defined in section 2032A(h)(3)(B)) or qualified exchange property (as defined in section 2032A(i)(3)), the increase in basis under paragraph (1) shall be made by reference to the property involuntarily converted or exchanged (as the case may be).
   (5)
   Election
   (A)
   In general
   An election under this subsection shall be made at such time and in such manner as the Secretary shall by regulations prescribe. Such an election, once made, shall be irrevocable.
   (B)
   Interest on recaptured amount
   If an election is made under this subsection with respect to any additional estate tax imposed under section 2032A(c)(1), for purposes of section 6601 (relating to interest on underpayments), the last date prescribed for payment of such tax shall be deemed to be the last date prescribed for payment of the tax imposed by section 2001 with respect to the estate of the decedent (as determined for purposes of section 6601).
   (d)
   Reduction in basis of automobile on which gas guzzler tax was imposed
   If—
   (1)
   the taxpayer acquires any automobile with respect to which a tax was imposed by section 4064, and
   (2)
   the use of such automobile by the taxpayer begins not more than 1 year after the date of the first sale for ultimate use of such automobile,
   the basis of such automobile shall be reduced by the amount of the tax imposed by section 4064 with respect to such automobile. In the case of importation, if the date of entry or withdrawal from warehouse for consumption is later than the date of the first sale for ultimate use, such later date shall be substituted for the date of such first sale in the preceding sentence.
   (e)
   Cross reference
   For treatment of separate mineral interests as one property, see section 614.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 299
   ; June 29, 1956, ch. 464, § 4(c),
   70 Stat. 407
   ;
   Pub. L. 85–866, title I
   , §§ 2(b), 64(d)(2),
   Sept. 2, 1958
   ,
   72 Stat. 1607
   , 1656;
   Pub. L. 86–69, § 3(d)
   ,
   June 25, 1959
   ,
   73 Stat. 139
   ;
   Pub. L. 87–834
   , §§ 2(f), 8(g)(2), 12(b)(4),
   Oct. 16, 1962
   ,
   76 Stat. 972
   , 998, 1031;
   Pub. L. 88–272, title II
   , §§ 203(a)(3)(C), 225(j)(2), 227(b)(5),
   Feb. 26, 1964
   ,
   78 Stat. 34
   , 93, 98;
   Pub. L. 91–172, title II, § 231(c)(3)
   , title V, §§ 504(c)(4), 516(c)(2)(B),
   Dec. 30, 1969
   ,
   83 Stat. 580
   , 633, 648;
   Pub. L. 94–455, title XIX, § 1901(a)(123)
   , (b)(1)(F)(ii), (21)(G), (29)(A), (30)(A), title XX, § 2005(a)(3),
   Oct. 4, 1976
   ,
   90 Stat. 1784
   , 1790, 1798, 1799, 1876;
   Pub. L. 95–472, § 4(b)
   ,
   Oct. 17, 1978
   ,
   92 Stat. 1335
   ;
   Pub. L. 95–600, title V, § 515(2)
   , title VI, § 601(b)(3), title VII, § 702(r)(3),
   Nov. 6, 1978
   ,
   92 Stat. 2884
   , 2896, 2938;
   Pub. L. 95–618, title I, § 101(b)(3)
   , title II, § 201(b),
   Nov. 9, 1978
   ,
   92 Stat. 3179
   , 3183;
   Pub. L. 96–222, title I
   , §§ 106(a)(2), (3), 107(a)(2)(C),
   Apr. 1, 1980
   ,
   94 Stat. 221
   , 222;
   Pub. L. 96–223, title IV, § 401(a)
   , (c)(1),
   Apr. 2, 1980
   ,
   94 Stat. 299
   , 300;
   Pub. L. 97–34, title II, § 212(d)(2)(G)
   , title IV, § 421(g),
   Aug. 13, 1981
   ,
   95 Stat. 239
   , 310;
   Pub. L. 97–248, title II
   , §§ 201(c)(2), 205(a)(5)(B),
   Sept. 3, 1982
   ,
   96 Stat. 418
   , 429;
   Pub. L. 97–354, § 5(a)(33)
   ,
   Oct. 19, 1982
   ,
   96 Stat. 1695
   ;
   Pub. L. 98–369, div. A, title I
   , §§ 43(a)(2), 53(d)(3), title II, § 211(b)(14), title IV, § 474(r)(23), title V, § 541(b)(2),
   July 18, 1984
   ,
   98 Stat. 558
   , 568, 756, 844, 890;
   Pub. L. 99–514, title II, § 241(b)(2)
   , title VII, § 701(e)(4)(D), title XIII, § 1303(b)(3), title XVIII, § 1899A(25),
   Oct. 22, 1986
   ,
   100 Stat. 2181
   , 2343, 2658, 2959;
   Pub. L. 100–647, title I
   , §§ 1006(j)(1)(B), 1018(u)(22),
   Nov. 10, 1988
   ,
   102 Stat. 3411
   , 3591;
   Pub. L. 101–194, title V, § 502(b)(2)
   ,
   Nov. 30, 1989
   ,
   103 Stat. 1755
   ;
   Pub. L. 101–508, title XI
   , §§ 11801(c)(1), 11812(b)(10), 11813(b)(19),
   Nov. 5, 1990
   ,
   104 Stat. 1388–522
   , 1388–535, 1388–555;
   Pub. L. 102–486, title XIX, § 1913(a)(3)(A)
   , (b)(2)(B),
   Oct. 24, 1992
   ,
   106 Stat. 3019
   , 3020;
   Pub. L. 103–66, title XIII
   , §§ 13114(b), 13213(a)(2)(F), 13261(f)(3),
   Aug. 10, 1993
   ,
   107 Stat. 431
   , 474, 539;
   Pub. L. 104–188, title I
   , §§ 1704(t)(56), 1807(c)(5),
   Aug. 20, 1996
   ,
   110 Stat. 1890
   , 1902;
   Pub. L. 105–34, title III
   , §§ 312(d)(6), 313(b)(1), title VII, § 701(b)(2),
   Aug. 5, 1997
   ,
   111 Stat. 840
   , 842, 869;
   Pub. L. 106–554, § 1(a)(7) [title I, § 116(b)(1)]
   ,
   Dec. 21, 2000
   ,
   114 Stat. 2763
   , 2763A–603;
   Pub. L. 107–16, title II, § 205(b)(3)
   ,
   June 7, 2001
   ,
   115 Stat. 53
   ;
   Pub. L. 108–357, title II, § 245(c)(2)
   , title III, §§ 338(b)(4), 339(d), title IV, § 413(c)(19),
   Oct. 22, 2004
   ,
   118 Stat. 1448
   , 1481, 1484, 1509;
   Pub. L. 109–58, title XIII
   , §§ 1331(b)(1), 1332(c), 1333(b)(1), 1335(b)(4), 1341(b)(2), 1342(b)(2),
   Aug. 8, 2005
   ,
   119 Stat. 1023
   , 1026, 1029, 1036, 1049, 1051;
   Pub. L. 109–135, title IV, § 412(nn)
   ,
   Dec. 21, 2005
   ,
   119 Stat. 2639
   ;
   Pub. L. 110–172
   , §§ 7(a)(1)(C), 11(a)(21), (22),
   Dec. 29, 2007
   ,
   121 Stat. 2481
   , 2486;
   Pub. L. 110–343, div. B, title II, § 205(d)(2)
   ,
   Oct. 3, 2008
   ,
   122 Stat. 3839
   ;
   Pub. L. 111–5, div. B, title I
   , §§ 1141(b)(3), 1142(b)(6),
   Feb. 17, 2009
   ,
   123 Stat. 328
   , 331;
   Pub. L. 111–148, title X, § 10909(b)(2)(L)
   , (c),
   Mar. 23, 2010
   ,
   124 Stat. 1023
   ;
   Pub. L. 111–312, title I, § 101(b)(1)
   ,
   Dec. 17, 2010
   ,
   124 Stat. 3298
   ;
   Pub. L. 113–295, div. A, title II
   , §§ 209(j)(2), 221(a)(2)(D), (34)(G), (75),
   Dec. 19, 2014
   ,
   128 Stat. 4030
   , 4037, 4042, 4049;
   Pub. L. 115–97, title I
   , §§ 13313(b), 13521(a), 13823(b),
   Dec. 22, 2017
   ,
   131 Stat. 2133
   , 2151, 2188;
   Pub. L. 115–141, div. U, title IV, § 401(a)(166)
   , (d)(4)(B)(iv),
   Mar. 23, 2018
   ,
   132 Stat. 1192
   , 1209;
   Pub. L. 117–169, title I, § 13301(f)(3)(B)
   ,
   Aug. 16, 2022
   ,
   136 Stat. 1945
   ;
   Pub. L. 119–21, title VII, § 70302(b)(10)
   ,
   July 4, 2025
   ,
   139 Stat. 192
   .)
   [1]
   So in original. The comma probably should be a semicolon.

-- TODO: Add type definitions
-- TODO: Add main functions
-- TODO: Add theorems to prove