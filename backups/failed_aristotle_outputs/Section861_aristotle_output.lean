/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: aca30a18-14f6-4ddd-882e-e02bca977efa

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
# IRC Section 861 - Income from sources within the United States

This file formalizes IRC §861 (Income from sources within the United States).

## References
- [26 USC §861](https://www.law.cornell.edu/uscode/text/26/861)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 861 - Income from sources within the United States
   U.S. Code
   Notes
   prev |
   next
   (a)
   Gross income from sources within United States
   The following items of gross income shall be treated as income from sources within the United States:
   (1)
   Interest
   Interest from the United States or the District of Columbia, and interest on bonds, notes, or other interest-bearing obligations of noncorporate residents or domestic corporations not including—
   (A)
   interest—
   (i)
   on deposits with a foreign branch of a domestic corporation or a domestic partnership if such branch is engaged in the commercial banking business, and
   (ii)
   on amounts satisfying the requirements of subparagraph (B) of
   section 871(i)(3)
   which are paid by a foreign branch of a domestic corporation or a domestic partnership, and
   (B)
   in the case of a foreign partnership, which is predominantly engaged in the active conduct of a trade or business outside the United States, any interest not paid by a trade or business engaged in by the partnership in the United States and not allocable to income which is effectively connected (or treated as effectively connected) with the conduct of a trade or business in the United States.
   (2)
   Dividends
   The amount received as dividends—
   (A)
   from a domestic corporation, or
   (B)
   from a foreign corporation unless less than 25 percent of the gross income from all sources of such foreign corporation for the 3-year period ending with the close of its taxable year preceding the declaration of such dividends (or for such part of such period as the corporation has been in existence) was effectively connected (or treated as effectively connected other than income described in section 884(d)(2)) with the conduct of a
   trade or business within the United States
   ; but only in an amount which bears the same ratio to such dividends as the gross income of the corporation for such period which was effectively connected (or treated as effectively connected other than income described in section 884(d)(2)) with the conduct of a
   trade or business within the United States
   bears to its gross income from all sources; but dividends (other than dividends for which a deduction is allowable under section 245(b)) from a foreign corporation shall, for purposes of subpart A of part III (relating to foreign tax credit), be treated as income from sources without the United States to the extent (and only to the extent) exceeding the amount which is 100/50th of the amount of the deduction allowable under section 245 in respect of such dividends, or
   (C)
   from a foreign corporation to the extent that such amount is required by section 243(e) (relating to certain dividends from foreign corporations) to be treated as dividends from a domestic corporation which is subject to taxation under this chapter, and to such extent subparagraph (B) shall not apply to such amount, or
   (D)
   from a DISC or former DISC (as defined in
   section 992(a)
   ) except to the extent attributable (as determined under regulations prescribed by the Secretary) to qualified export receipts described in section 993(a)(1) (other than interest and gains described in section 995(b)(1)).
   In the case of any dividend from a 20-percent owned corporation (as defined in
   section 243(c)(2)
   ), subparagraph (B) shall be applied by substituting “100/65th” for “100/50th”.
   (3)
   Personal services
   Compensation for labor or personal services performed in the United States; except that compensation for labor or services performed in the United States shall not be deemed to be income from sources within the United States if—
   (A)
   the labor or services are performed by a nonresident alien individual temporarily present in the United States for a period or periods not exceeding a total of 90 days during the taxable year,
   (B)
   such compensation does not exceed $3,000 in the aggregate, and
   (C)
   the compensation is for labor or services performed as an employee of or under a contract with—
   (i)
   a nonresident alien, foreign partnership, or foreign corporation, not engaged in
   trade or business within the United States
   , or
   (ii)
   an individual who is a citizen or resident of the United States, a domestic partnership, or a domestic corporation, if such labor or services are performed for an office or place of business maintained in a foreign country or in a possession of the United States by such individual, partnership, or corporation.
   In addition, compensation for labor or services performed in the United States shall not be deemed to be income from sources within the United States if the labor or services are performed by a nonresident alien individual in connection with the individual’s temporary presence in the United States as a regular member of the crew of a foreign vessel engaged in transportation between the United States and a foreign country or a possession of the United States.
   (4)
   Rentals and royalties
   Rentals or royalties from property located in the United States or from any interest in such property, including rentals or royalties for the use of or for the privilege of using in the United States patents, copyrights, secret processes and formulas, good will, trade-marks, trade brands, franchises, and other like property.
   (5)
   Disposition of United States real property interest
   Gains, profits, and income from the
   disposition
   of a United States real property interest (as defined in
   section 897(c)
   ).
   (6)
   Sale or exchange of inventory property
   Gains, profits, and income derived from the purchase of inventory property (within the meaning of section 865(i)(1)) without the United States (other than within a possession of the United States) and its sale or exchange within the United States.
   (7)
   Amounts received as underwriting income (as defined in
   section 832(b)(3)
   ) derived from the issuing (or reinsuring) of any insurance or annuity contract—
   (A)
   in connection with property in, liability arising out of an activity in, or in connection with the lives or health of residents of, the United States, or
   (B)
   in connection with risks not described in subparagraph (A) as a result of any arrangement whereby another corporation receives a substantially equal amount of premiums or other consideration in respect to issuing (or reinsuring) any insurance or annuity contract in connection with property in, liability arising out of activity in, or in connection with the lives or health of residents of, the United States.
   (8)
   Social security benefits
   Any social security benefit (as defined in
   section 86(d)
   ).
   (9)
   Guarantees
   Amounts received, directly or indirectly, from—
   (A)
   a noncorporate resident or domestic corporation for the provision of a guarantee of any indebtedness of such resident or corporation, or
   (B)
   any foreign person for the provision of a guarantee of any indebtedness of such person, if such amount is connected with income which is effectively connected (or treated as effectively connected) with the conduct of a trade or business in the United States.
   (b)
   Taxable income from sources within United States
   From the items of gross income specified in subsection (a) as being income from sources within the United States there shall be deducted the expenses, losses, and other deductions properly apportioned or allocated thereto and a ratable part of any expenses, losses, or other deductions which cannot definitely be allocated to some item or class of gross income. The remainder, if any, shall be included in full as taxable income from sources within the United States. In the case of an individual who does not itemize deductions, an amount equal to the standard deduction shall be considered a deduction which cannot definitely be allocated to some item or class of gross income.
   (c)
   Special rule for application of subsection (a)(2)(B)
   For purposes of subsection (a)(2)(B), if the foreign corporation has no gross income from any source for the 3-year period (or part thereof) specified, the requirements of such subsection shall be applied with respect to the taxable year of such corporation in which the payment of the dividend is made.
   (d)
   Income from certain railroad rolling stock treated as income from sources within the United States
   (1)
   General rule
   For purposes of subsection (a) and section 862(a), if—
   (A)
   a taxpayer leases railroad rolling stock which is
   section 1245
   property (as defined in section 1245(a)(3)) to a domestic common carrier by railroad or a corporation which is controlled, directly or indirectly, by one or more such common carriers, and
   (B)
   the use under such lease is expected to be use within the United States,
   all amounts includible in gross income by the taxpayer with respect to such railroad rolling stock (including gain from sale or other
   disposition
   of such railroad rolling stock) shall be treated as income from sources within the United States. The requirements of subparagraph (B) of the preceding sentence shall be treated as satisfied if the only expected use outside the United States is use by a person (whether or not a United States person) in Canada or Mexico on a temporary basis which is not expected to exceed a total of 90 days in any taxable year.
   (2)
   Paragraph (1) not to apply where lessor is a member of controlled group which includes a railroad
   Paragraph (1) shall not apply to a lease between two members of the same controlled group of corporations (as defined in
   section 1563
   ) if any member of such group is a domestic common carrier by railroad or a switching or terminal company all of whose stock is owned by one or more domestic common carriers by railroad.
   (3)
   Denial of foreign tax credit
   No credit shall be allowed under
   section 901
   for any payments to foreign countries with respect to any amount received by the taxpayer with respect to railroad rolling stock which is subject to paragraph (1).
   (e)
   Cross reference
   For treatment of interest paid by the branch of a foreign corporation, see section 884(f).
   (Aug. 16, 1954, ch. 736,
   68A Stat. 275
   ;
   Pub. L. 86–779, § 3(b)
   ,
   Sept. 14, 1960
   ,
   74 Stat. 998
   ;
   Pub. L. 87–834, § 9(c)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 1001
   ;
   Pub. L. 89–809, title I, § 102(a)(1)
   –(3), (b), (c),
   Nov. 13, 1966
   ,
   80 Stat. 1541–1543
   ;
   Pub. L. 91–172, title IV, § 435(a)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 625
   ;
   Pub. L. 92–9, § 3(a)(2)
   ,
   Apr. 1, 1971
   ,
   85 Stat. 15
   ;
   Pub. L. 92–178, title III, § 314(a)
   , title V, § 503,
   Dec. 10, 1971
   ,
   85 Stat. 528
   , 550;
   Pub. L. 93–625
   , §§ 8, 9(a),
   Jan. 3, 1975
   ,
   88 Stat. 2116
   ;
   Pub. L. 94–455, title X
   , §§ 1036(a), 1041, 1051(h)(3), title XIX, §§ 1901(b)(26)(A), (B), (c)(7), 1904(b)(10)(B), 1906(b)(13)(A),
   Oct. 4, 1976
   ,
   90 Stat. 1633
   , 1634, 1647, 1798, 1803, 1817, 1834;
   Pub. L. 95–30, title I, § 102(b)(9)
   ,
   May 23, 1977
   ,
   91 Stat. 138
   ;
   Pub. L. 95–600, title III, § 370(a)
   , title V, § 540(a),
   Nov. 6, 1978
   ,
   92 Stat. 2858
   , 2887;
   Pub. L. 96–499, title XI, § 1124
   ,
   Dec. 5, 1980
   ,
   94 Stat. 2690
   ;
   Pub. L. 96–605, title I, § 104(a)
   ,
   Dec. 28, 1980
   ,
   94 Stat. 3523
   ;
   Pub. L. 98–21, title I, § 121(d)
   ,
   Apr. 20, 1983
   ,
   97 Stat. 83
   ;
   Pub. L. 99–514, title I, § 104(b)(11)
   , title XII, §§ 1211(b)(1)(B), 1212(d), 1214(a), (b), (c)(5), 1241(b),
   Oct. 22, 1986
   ,
   100 Stat. 2105
   , 2536, 2539, 2541–2543, 2579;
   Pub. L. 100–203, title X, § 10221(d)(4)
   ,
   Dec. 22, 1987
   ,
   101 Stat. 1330–409
   ;
   Pub. L. 100–647, title I
   , §§ 1012(g)(3), (i)(10), (14)(B), (q)(7), (9), (15), 1018(u)(39),
   Nov. 10, 1988
   ,
   102 Stat. 3501
   , 3509, 3510, 3524, 3525, 3592;
   Pub. L. 101–239, title VII
   , §§ 7811(i)(2), 7841(d)(9),
   Dec. 19, 1989
   ,
   103 Stat. 2409
   , 2428;
   Pub. L. 101–508, title XI
   , §§ 11801(a)(29), (c)(6)(C), (14), 11813(b)(17),
   Nov. 5, 1990
   ,
   104 Stat. 1388–521
   , 1388–524, 1388–527, 1388–555;
   Pub. L. 104–188, title I, § 1702(h)(9)
   ,
   Aug. 20, 1996
   ,
   110 Stat. 1874
   ;
   Pub. L. 105–34, title XI, § 1174(a)(1)
   ,
   Aug. 5, 1997
   ,
   111 Stat. 989
   ;
   Pub. L. 107–16, title VI, § 621(a)
   ,
   June 7, 2001
   ,
   115 Stat. 111
   ;
   Pub. L. 108–357, title IV, § 410(a)
   ,
   Oct. 22, 2004
   ,
   118 Stat. 1500
   ;
   Pub. L. 111–226, title II, § 217(a)
   , (c)(1),
   Aug. 10, 2010
   ,
   124 Stat. 2400
   , 2402;
   Pub. L. 111–240, title II, § 2122(a)
   ,
   Sept. 27, 2010
   ,
   124 Stat. 2567
   ;
   Pub. L. 115–97, title I, § 13002(e)
   ,
   Dec. 22, 2017
   ,
   131 Stat. 2100
   ;
   Pub. L. 115–141, div. U, title IV, § 401(d)(1)(D)(ix)
   ,
   Mar. 23, 2018
   ,
   132 Stat. 1207
   .)

-- TODO: Add type definitions
-- TODO: Add main functions
-- TODO: Add theorems to prove