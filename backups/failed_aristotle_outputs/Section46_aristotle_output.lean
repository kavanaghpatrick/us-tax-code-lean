/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f4203568-b0fb-4ba6-af22-4586106d1785

Aristotle encountered an error processing this file. The team has been notified.

-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: efbba53a-26b3-40a2-aeb5-8f058f872336

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
# IRC Section 46 - Amount of credit

This file formalizes IRC §46 (Amount of credit).

## References
- [26 USC §46](https://www.law.cornell.edu/uscode/text/26/46)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 46 - Amount of credit
   U.S. Code
   Notes
   Authorities (CFR)
   prev |
   next
   For purposes of section 38, the amount of the investment credit determined under this section for any taxable year shall be the sum of—
   (1)
   the rehabilitation credit,
   (2)
   the energy credit,
   (3)
   the qualifying advanced coal project credit,
   (4)
   the qualifying gasification project credit,
   (5)
   the
   qualifying advanced energy project
   credit,
   (6)
   the advanced manufacturing investment credit, and
   (7)
   the clean electricity investment credit.
   (Added
   Pub. L. 87–834, § 2(b)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 963
   ; amended
   Pub. L. 88–272, title II, § 201(d)(4)
   ,
   Feb. 26, 1964
   ,
   78 Stat. 32
   ;
   Pub. L. 89–384, § 1(c)(1)
   ,
   Apr. 8, 1966
   ,
   80 Stat. 102
   ;
   Pub. L. 89–389, § 2(b)(5)
   ,
   Apr. 14, 1966
   ,
   80 Stat. 114
   ;
   Pub. L. 89–800, § 3
   ,
   Nov. 8, 1966
   ,
   80 Stat. 1514
   ;
   Pub. L. 90–225, § 2(a)
   ,
   Dec. 27, 1967
   ,
   81 Stat. 731
   ;
   Pub. L. 91–172, title III, § 301(b)(4)
   , title IV, § 401(e)(1), title VII, § 703(b),
   Dec. 30, 1969
   ,
   83 Stat. 585
   , 603, 666;
   Pub. L. 92–178, title I
   , §§ 102(a)(1), (b), 105(a)–(c), 106(a)–(c), 107(a)(1), 108(a),
   Dec. 10, 1971
   ,
   85 Stat. 499
   , 503, 506, 507;
   Pub. L. 93–406, title II
   , §§ 2001(g)(2)(B), 2002(g)(2), 2005(c)(4),
   Sept. 2, 1974
   ,
   88 Stat. 957
   , 968, 991;
   Pub. L. 94–12, title III, § 301(a)
   , (b)(1)–(3), 302(a), (b)(1),
   Mar. 29, 1975
   ,
   89 Stat. 36
   , 37, 40, 43;
   Pub. L. 94–455, title V, § 503(b)(4)
   , title VIII, §§ 802(a), (b)(1)–(5), 803(a), (b)(1), 805(a), title XVI, § 1607(b)(1)(B), title XVII, §§ 1701(b), 1703, title XIX, §§ 1901(a)(4), (b)(1)(C), 1906(b)(13)(A), title XXI, § 2112(a)(2),
   Oct. 4, 1976
   ,
   90 Stat. 1562
   , 1580–1583, 1596, 1756, 1759, 1761, 1764, 1790, 1834, 1905;
   Pub. L. 95–600, title I, § 141(e)
   , (f)(2), title III, §§ 311(a), (c), 312(a), (b), (c)(2), 313(a), 316(a), (b)(1), (2), title VII, § 703(a)(1), (2), (j)(9),
   Nov. 6, 1978
   ,
   92 Stat. 2794
   , 2795, 2824–2826, 2829, 2939, 2941;
   Pub. L. 95–618, title II, § 241(a)
   , title III, § 301(a), (c)(1),
   Nov. 9, 1978
   ,
   92 Stat. 3192
   , 3194, 3199;
   Pub. L. 96–222, title I
   , §§ 101(a)(7)(A), (L)(iii)(I), (v)(I), (M)(i), 103(a)(2)(A), (B)(i)–(iii), (3), (4)(A), 107(a)(3)(A),
   Apr. 1, 1980
   ,
   94 Stat. 197
   , 200, 201, 208, 209, 223;
   Pub. L. 96–223, title II
   , §§ 221(a), 222(e)(2), 223(b)(1),
   Apr. 2, 1980
   ,
   94 Stat. 260
   , 263, 266;
   Pub. L. 97–34, title II
   , §§ 207(c)(1), 211(a)(1), (b), (d), (e)(1), (2), (f)(1), 212(a)(1), (2), title III, §§ 302(c)(3), (d)(1), 332(a),
   Aug. 13, 1981
   ,
   95 Stat. 225
   , 227–229, 235, 236, 272, 274, 296;
   Pub. L. 97–248, title II, § 201(d)(8)(A)
   , formerly § 201(c)(8)(A), §§ 205(b), 265(b)(2)(A)(i),
   Sept. 3, 1982
   ,
   96 Stat. 420
   , 430, 547, renumbered § 201(d)(8)(A),
   Pub. L. 97–448, title III, § 306(a)(1)(A)(i)
   ,
   Jan. 12, 1983
   ,
   96 Stat. 2400
   ;
   Pub. L. 97–354, § 5(a)(4)
   –(6),
   Oct. 19, 1982
   ,
   96 Stat. 1692
   ;
   Pub. L. 97–424, title V
   , §§ 541(b), 546(b),
   Jan. 6, 1983
   ,
   96 Stat. 2192
   , 2199;
   Pub. L. 97–448, title I, § 102(e)(1)
   , (f)(5), title II, § 202(f),
   Jan. 12, 1983
   ,
   96 Stat. 2370
   , 2372, 2396;
   Pub. L. 98–21, title I, § 122(c)(1)
   ,
   Apr. 20, 1983
   ,
   97 Stat. 87
   ;
   Pub. L. 98–369, div. A, title I
   , §§ 16(a), 31(f), 113(b)(2)(B), title IV, §§ 431(a), (b)(1), (d)(1)–(3), 474(
   o
   )(1)–(7), title VII, § 713(c)(1)(C),
   July 18, 1984
   ,
   98 Stat. 505
   , 521, 637, 805, 807, 810, 834–836, 957;
   Pub. L. 99–514, title II
   , §§ 201(d)(7)(B), 251(a), title IV, § 421(a), (b), title XVIII, §§ 1802(a)(6), (8), 1844(a), (b)(3), (5), 1847(b)(11), 1848(a),
   Oct. 22, 1986
   ,
   100 Stat. 2141
   , 2183, 2229, 2789, 2855, 2857;
   Pub. L. 100–647, title I
   , §§ 1002(a)(4), (15), (17), (25), 1009(a)(1), 1013(a)(44), title IV, § 4006,
   Nov. 10, 1988
   ,
   102 Stat. 3353
   , 3355, 3356, 3445, 3545, 3652;
   Pub. L. 101–239, title VII
   , §§ 7106, 7814(d),
   Dec. 19, 1989
   ,
   103 Stat. 2306
   , 2413;
   Pub. L. 101–508, title XI
   , §§ 11406, 11813(a),
   Nov. 5, 1990
   ,
   104 Stat. 1388–474
   , 1388–536;
   Pub. L. 108–357, title III, § 322(d)(1)
   ,
   Oct. 22, 2004
   ,
   118 Stat. 1475
   ;
   Pub. L. 109–58, title XIII, § 1307(a)
   ,
   Aug. 8, 2005
   ,
   119 Stat. 999
   ;
   Pub. L. 111–5, div. B, title I, § 1302(a)
   ,
   Feb. 17, 2009
   ,
   123 Stat. 345
   ;
   Pub. L. 111–148, title IX, § 9023(b)
   ,
   Mar. 23, 2010
   ,
   124 Stat. 880
   ;
   Pub. L. 113–295, div. A, title II, § 220(c)
   ,
   Dec. 19, 2014
   ,
   128 Stat. 4035
   ;
   Pub. L. 117–167, div. A, § 107(d)(1)
   ,
   Aug. 9, 2022
   ,
   136 Stat. 1398
   ;
   Pub. L. 117–169, title I, § 13702(b)(1)
   ,
   Aug. 16, 2022
   ,
   136 Stat. 1996
   .)

-- TODO: Add type definitions
-- TODO: Add main functions