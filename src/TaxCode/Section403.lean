/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b6d09c0d-1837-45d6-9521-6bade0f2a4ee

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
# IRC Section 403 - Taxation of employee annuities

This file formalizes IRC §403 (Taxation of employee annuities).

## References
- [26 USC §403](https://www.law.cornell.edu/uscode/text/26/403)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 403 - Taxation of employee annuities
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   Taxability of beneficiary under a qualified annuity plan
   (1)
   Distributee taxable under section 72
   If an annuity contract is purchased by an employer for an
   employee
   under a plan which meets the requirements of section 404(a)(2) (whether or not the employer deducts the amounts paid for the contract under such section), the amount actually distributed to any distributee under the contract shall be taxable to the distributee (in the year in which so distributed) under section 72 (relating to annuities).
   (2)
   Special rule for health and long-term care insurance
   To the extent provided in section 402(l), paragraph (1) shall not apply to the amount distributed under the contract which is otherwise includible in gross income under this subsection.
   (3)
   Self-employed individuals
   For purposes of this subsection, the term “
   employee
   ” includes an individual who is an
   employee
   within the meaning of section 401(c)(1), and the employer of such individual is the person treated as his employer under section 401(c)(4).
   (4)
   Rollover amounts
   (A)
   General rule
   If—
   (i)
   any portion of the balance to the credit of an
   employee
   in an
   employee
   annuity described in paragraph (1) is paid to him in an eligible rollover distribution (within the meaning of
   section 402(c)(4)
   ),
   (ii)
   the
   employee
   transfers any portion of the property he receives in such distribution to an eligible retirement plan, and
   (iii)
   in the case of a distribution of property other than money, the amount so transferred consists of the property distributed,
   then such distribution (to the extent so transferred) shall not be includible in gross income for the taxable year in which paid.
   (B)
   Certain rules made applicable
   The rules of paragraphs (2) through (7) and (11) and (9) of section 402(c) and section 402(f) shall apply for purposes of subparagraph (A).
   (5)
   Direct trustee-to-trustee transfer
   Any amount transferred in a direct trustee-to-trustee transfer in accordance with
   section 401(a)(31)
   shall not be includible in gross income for the taxable year of such transfer.
   (6)
   Qualified long-term care distributions
   An annuity contract shall not fail to be subject to this subsection solely by reason of allowing distributions to which
   section 401(a)(39)
   applies.
   (b)
   Taxability of beneficiary under annuity purchased by
   section 501(c)(3)
   organization or public school
   (1)
   General rule
   If—
   (A)
   an annuity contract is purchased—
   (i)
   for an
   employee
   by an employer described in
   section 501(c)(3)
   which is exempt from tax under section 501(a),
   (ii)
   for an
   employee
   (other than an
   employee
   described in clause (i)), who performs services for an educational organization described in section 170(b)(1) (A)(ii), by an employer which is a State, a political subdivision of a State, or an agency or instrumentality of any one or more of the foregoing, or
   (iii)
   for the minister described in
   section 414(e)(5)(A)
   by the minister or by an employer,
   (B)
   such annuity contract is not subject to subsection (a),
   (C)
   the
   employee
   ’s rights under the contract are nonforfeitable, except for failure to pay future premiums,
   (D)
   except in the case of a contract purchased by a
   church
   , such contract is purchased under a plan which meets the nondiscrimination requirements of paragraph (12), and
   (E)
   in the case of a contract purchased under a salary reduction agreement, the contract meets the requirements of section 401(a)(30),
   then contributions and other additions by such employer for such annuity contract shall be excluded from the gross income of the
   employee
   for the taxable year to the extent that the aggregate of such contributions and additions (when expressed as an annual addition (within the meaning of section 415(c)(2))) does not exceed the applicable limit under section 415. The amount actually distributed to any distributee under such contract shall be taxable to the distributee (in the year in which so distributed) under section 72 (relating to annuities). For purposes of applying the rules of this subsection to contributions and other additions by an employer for a taxable year, amounts transferred to a contract described in this paragraph by reason of a rollover contribution described in paragraph (8) of this subsection or section 408(d)(3)(A)(ii) shall not be considered contributed by such employer.
   (2)
   Special rule for health and long-term care insurance
   To the extent provided in section 402(l), paragraph (1) shall not apply to the amount distributed under the contract which is otherwise includible in gross income under this subsection.
   (3)
   Includible compensation
   For purposes of this subsection, the term “
   includible compensation
   ” means, in the case of any
   employee,
   the amount of compensation which is received from the employer described in paragraph (1)(A), and which is includible in gross income (computed without regard to section 911) for the most recent period (ending not later than the close of the taxable year) which under paragraph (4) may be counted as one year of service, and which precedes the taxable year by no more than five years. Such term does not include any amount contributed by the employer for any annuity contract to which this subsection applies. Such term includes—
   (A)
   any
   elective deferral
   (as defined in
   section 402(g)(3)
   ), and
   (B)
   any amount which is contributed or deferred by the employer at the election of the
   employee
   and which is not includible in the gross income of the
   employee
   by reason of section 125, 132(f)(4), or 457.
   (4)
   Years of service
   In determining the number of years of service for purposes of this subsection, there shall be included—
   (A)
   one year for each full year during which the individual was a full-time
   employee
   of the organization purchasing the annuity for him, and
   (B)
   a fraction of a year (determined in accordance with regulations prescribed by the Secretary) for each full year during which such individual was a part-time
   employee
   of such organization and for each part of a year during which such individual was a full-time or part-time
   employee
   of such organization.
   In no case shall the number of years of service be less than one.
   (5)
   Application to more than one annuity contract
   If for any taxable year of the
   employee
   this subsection applies to 2 or more annuity contracts purchased by the employer, such contracts shall be treated as one contract.
   [(6)
   Repealed.
   Pub. L. 107–147, title IV, § 411(p)(2)
   ,
   Mar. 9, 2002
   ,
   116 Stat. 50
   ]
   (7)
   Custodial accounts
   (A)
   Amounts paid treated as contributions
   For purposes of this title, amounts paid by an employer described in paragraph (1)(A) to a custodial account which satisfies the requirements of
   section 401(f)(2)
   shall be treated as amounts contributed by him for an annuity contract for his
   employee
   if the amounts are to be held in that custodial account and are invested in
   regulated investment company
   stock or a group trust intended to satisfy the requirements of
   Internal Revenue Service
   Revenue Ruling 81–100 (or any successor guidance), and under the custodial account—
   (i)
   no such amounts may be paid or made available to any distributee (unless such amount is a distribution to which
   section 72(t)(2)(G)
   applies) before—
   (I)
   the
   employee
   dies,
   (II)
   the
   employee
   attains age 59½,
   (III)
   the
   employee
   has a severance from employment,
   (IV)
   the
   employee
   becomes disabled (within the meaning of
   section 72(m)(7)
   ),
   (V)
   subject to the provisions of paragraph (17), the
   employee
   encounters financial hardship,
   (VI)
   except as may be otherwise provided by regulations, with respect to amounts invested in a lifetime income investment (as defined in
   section 401(a)(38)(B)(ii)
   ), the date that is 90 days prior to the date that such lifetime income investment may no longer be held as an investment option under the contract, or
   (VII)
   as provided for distributions to which
   section 401(a)(39)
   applies, and
   (ii)
   in the case of amounts described in clause (i)(VI), such amounts will be distributed only in the form of a qualified distribution (as defined in
   section 401(a)(38)(B)(i)
   ) or a
   qualified plan
   distribution annuity contract (as defined in section 401(a)(38)(B)(iv)).
   (B)
   Account treated as plan
   For purposes of this title, a custodial account which satisfies the requirements of
   section 401(f)(2)
   shall be treated as an organization described in section 401(a) solely for purposes of subchapter F and subtitle F with respect to amounts received by it (and income from investment thereof).
   (C)
   Regulated investment company
   For purposes of this paragraph, the term “
   regulated investment company
   ” means a domestic corporation which is a
   regulated investment company
   within the meaning of section 851(a).
   (D)
   Employee certification
   In determining whether a distribution is upon the financial hardship of an
   employee
   , the administrator of the plan may rely on a written certification by the
   employee
   that the distribution is—
   (i)
   on account of a financial need of a type which is deemed in regulations prescribed by the Secretary to be an immediate and heavy financial need, and
   (ii)
   not in excess of the amount required to satisfy such financial need, and
   that the
   employee
   has no alternative means reasonably available to satisfy such financial need. The Secretary may provide by regulations for exceptions to the rule of the preceding sentence in cases where the
   plan administrator
   has actual knowledge to the contrary of the
   employee
   ’s certification, and for procedures for addressing cases of
   employee
   misrepresentation.
   (8)
   Rollover amounts
   (A)
   General rule
   If—
   (i)
   any portion of the balance to the credit of an
   employee
   in an annuity contract described in paragraph (1) is paid to him in an eligible rollover distribution (within the meaning of
   section 402(c)(4)
   ),
   (ii)
   the
   employee
   transfers any portion of the property he receives in such distribution to an eligible retirement plan described in section 402(c)(8)(B), and
   (iii)
   in the case of a distribution of property other than money, the property so transferred consists of the property distributed,
   then such distribution (to the extent so transferred) shall not be includible in gross income for the taxable year in which paid.
   (B)
   Certain rules made applicable
   The rules of paragraphs (2) through (7), (9), and (11) of section 402(c) and section 402(f) shall apply for purposes of subparagraph (A), except that section 402(f) shall be applied to the payor in lieu of the
   plan administrator
   .
   (9)
   Retirement income accounts provided by churches, etc.
   (A)
   Amounts paid treated as contributions
   For purposes of this title—
   (i)
   a
   retirement income account
   shall be treated as an annuity contract described in this subsection, and
   (ii)
   amounts paid by an employer described in paragraph (1)(A) to a
   retirement income account
   shall be treated as amounts contributed by the employer for an annuity contract for the
   employee
   on whose behalf such account is maintained.
   (B)
   Retirement income account
   For purposes of this paragraph, the term “
   retirement income account
   ” means a defined contribution program established or maintained by a
   church,
   or a convention or association of
   churches,
   including an organization described in section 414(e)(3)(A), to provide benefits under
   section 403(b)
   for an
   employee
   described in paragraph (1) (including an
   employee
   described in section 414(e)(3)(B)) or his beneficiaries.
   (10)
   Distribution requirements
   Under regulations prescribed by the Secretary, this subsection shall not apply to any annuity contract (or to any custodial account described in paragraph (7) or
   retirement income account
   described in paragraph (9)) unless requirements similar to the requirements of sections 401(a)(9) and 401(a)(31) are met (and requirements similar to the incidental death benefit requirements of section 401(a) are met) with respect to such annuity contract (or custodial account or
   retirement income account
   ). Any amount transferred in a direct trustee-to-trustee transfer in accordance with section 401(a)(31) shall not be includible in gross income for the taxable year of the transfer.
   (11)
   Requirement that distributions not begin before age 59½, severance from employment, death, or disability
   This subsection shall not apply to any annuity contract unless under such contract distributions attributable to contributions made pursuant to a salary reduction agreement (within the meaning of
   section 402(g)(3)(C)
   ) may be paid only—
   (A)
   when the
   employee
   attains age 59½, has a severance from employment, dies, or becomes disabled (within the meaning of
   section 72(m)(7)
   ),
   (B)
   subject to the provisions of paragraph (17), in the case of hardship,
   (C)
   for distributions to which
   section 72(t)(2)(G)
   applies,
   (D)
   except as may be otherwise provided by regulations, with respect to amounts invested in a lifetime income investment (as defined in
   section 401(a)(38)(B)(ii)
   )—
   (i)
   on or after the date that is 90 days prior to the date that such lifetime income investment may no longer be held as an investment option under the contract, and
   (ii)
   in the form of a qualified distribution (as defined in
   section 401(a)(38)(B)(i)
   ) or a
   qualified plan
   distribution annuity contract (as defined in section 401(a)(38)(B)(iv)), or
   (E)
   for distributions to which
   section 401(a)(39)
   applies.
   In determining whether a distribution is upon hardship of an
   employee
   , the administrator of the plan may rely on a written certification by the
   employee
   that the distribution is on account of a financial need of a type which is deemed in regulations prescribed by the Secretary to be an immediate and heavy financial need and is not in excess of the amount required to satisfy such financial need, and that the
   employee
   has no alternative means reasonably available to satisfy such financial need. The Secretary may provide by regulations for exceptions to the rule of the preceding sentence in cases where the
   plan administrator
   has actual knowledge to the contrary of the
   employee
   ’s certification, and for procedures for addressing cases of
   employee
   misrepresentation.
   (12)
   Nondiscrimination requirements
   (A)
   In general
   For purposes of paragraph (1)(D), a plan meets the nondiscrimination requirements of this paragraph if—
   (i)
   with respect to contributions not made pursuant to a salary reduction agreement, such plan meets the requirements of paragraphs (4), (5), (17), and (26) of section 401(a), section 401(m), and
   section 410(b)
   in the same manner as if such plan were described in section 401(a), and
   (ii)
   all
   employees
   of the organization may elect to have the employer make contributions of more than $200 pursuant to a salary reduction agreement if any
   employee
   of the organization may elect to have the organization make contributions for such contracts pursuant to such agreement.
   For purposes of clause (i), a contribution shall be treated as not made pursuant to a salary reduction agreement if under the agreement it is made pursuant to a 1-time irrevocable election made by the
   employee
   at the time of initial eligibility to participate in the agreement or is made pursuant to a similar arrangement involving a one-time irrevocable election specified in regulations. For purposes of clause (ii), there may be excluded any
   employee
   who is a participant in an eligible deferred compensation plan (within the meaning of section 457) or a qualified cash or deferred arrangement of the organization or another annuity contract described in this subsection. Any nonresident alien described in section 410(b)(3)(C) may also be excluded. Subject to the conditions applicable under section 410(b)(4) and section 202(c) of the
   Employee Retirement Income Security Act of 1974
   , there may be excluded for purposes of this subparagraph
   employees
   who are students performing services described in section 3121(b)(10) and
   employees
   who normally work less than 20 hours per week. The fact that the employer offers
   matching contributions
   on account of qualified student loan payments as described in section 401(m)(13) shall not be taken into account in determining whether the arrangement satisfies the requirements of clause (ii) (and any regulation thereunder). A plan shall not fail to satisfy clause (ii) solely by reason of offering a de minimis financial incentive (not derived from plan assets) to
   employees
   to elect to have the employer make contributions pursuant to a salary reduction agreement.
   (B)
   Church
   For purposes of paragraph (1)(D), the term “
   church
   ” has the meaning given to such term by
   section 3121(w)(3)(A).
   Such term shall include any qualified
   church-
   controlled organization (as defined in section 3121(w)(3)(B)).
   (C)
   State and local governmental plans
   For purposes of paragraph (1)(D), the requirements of subparagraph (A)(i) (other than those relating to
   section 401(a)(17)
   ) shall not apply to a
   governmental plan
   (within the meaning of section 414(d)) maintained by a State or local government or political subdivision thereof (or agency or instrumentality thereof).
   (D)
   Rules relating to certain part-time employees
   (i)
   [1]
   In general
   In the case of
   employees
   who are eligible to participate in the agreement solely by reason of section 202(c)(1)(B) of the
   Employee Retirement Income Security Act of 1974
   —
   (I)
   notwithstanding section 401(a)(4), an employer shall not be required to make nonelective or
   matching contributions
   on behalf of such
   employees
   even if such contributions are made on behalf of other
   employees
   eligible to participate in the plan, and
   (II)
   the employer may elect to exclude such
   employees
   from the application of subsections (a)(4), (k)(3), (k)(12), (k)(13), and (m)(2) of section 401 and section 410(b).
   (13)
   Trustee-to-trustee transfers to purchase permissive service credit
   No amount shall be includible in gross income by reason of a direct trustee-to-trustee transfer to a defined benefit
   governmental plan
   (as defined in
   section 414(d)
   ) if such transfer is—
   (A)
   for the purchase of permissive service credit (as defined in
   section 415(n)(3)(A)
   ) under such plan, or
   (B)
   a repayment to which
   section 415
   does not apply by reason of subsection (k)(3) thereof.
   (14)
   Death benefits under USERRA-qualified active military service
   This subsection shall not apply to an annuity contract unless such contract meets the requirements of section 401(a)(37).
   (15)
   Multiple employer plans
   (A)
   In general
   Except in the case of a
   church
   plan, this subsection shall not be treated as failing to apply to an annuity contract solely by reason of such contract being purchased under a plan maintained by more than 1 employer.
   (B)
   Treatment of employers failing to meet requirements of plan
   (i)
   In general
   In the case of a plan maintained by more than 1 employer, this subsection shall not be treated as failing to apply to an annuity contract held under such plan merely because of one or more employers failing to meet the requirements of this subsection if such plan satisfies rules similar to the rules of
   section 413(e)(2)
   with respect to any such employer failure.
   (ii)
   Additional requirements in case of non-governmental plans
   A plan shall not be treated as meeting the requirements of this subparagraph unless the plan satisfies rules similar to the rules of subparagraph (A) or (B) of section 413(e)(1), except in the case of a multiple employer plan maintained solely by any of the following: A State, a political subdivision of a State, or an agency or instrumentality of any one or more of the foregoing.
   (16)
   Safe harbor deferral-only plans for employers with no retirement plan
   (A)
   In general
   A
   safe harbor deferral-only plan
   maintained by an
   eligible employer
   shall be treated as meeting the requirements of paragraph (12).
   (B)
   Safe harbor deferral-only plan
   For purposes of this paragraph, the term “
   safe harbor deferral-only plan
   ” means any plan which meets—
   (i)
   the automatic deferral requirements of subparagraph (C),
   (ii)
   the contribution limitations of subparagraph (D), and
   (iii)
   the requirements of subparagraph (E) of section 401(k)(13).
   (C)
   Automatic deferral
   (i)
   In general
   The requirements of this subparagraph are met if, under the plan, each
   eligible employee
   is treated as having elected to have the employer make elective contributions in an amount equal to a
   qualified percentage
   of compensation.
   (ii)
   Election out
   The election treated as having been made under clause (i) shall cease to apply with respect to any
   eligible employee
   if such
   eligible employee
   makes an affirmative election—
   (I)
   to not have such contributions made, or
   (II)
   to make elective contributions at a level specified in such affirmative election.
   (iii)
   Qualified percentage
   For purposes of this subparagraph, the term “
   qualified percentage
   ” means, with respect to any
   employee,
   any percentage determined under the plan if such percentage is applied uniformly and is not less than 3 or more than 15 percent.
   (D)
   Contribution limitations
   (i)
   In general
   The requirements of this subparagraph are met if, under the plan—
   (I)
   the only contributions which may be made are elective contributions of
   eligible employees
   , and
   (II)
   the aggregate amount of such elective contributions which may be made with respect to any
   employee
   for any calendar year shall not exceed $6,000.
   (ii)
   Cost-of-living adjustment
   In the case of any calendar year beginning after
   December 31, 2024
   , the $6,000 amount under clause (i) shall be adjusted in the same manner as under section 402(g)(4), except that “2023” shall be substituted for “2005”.
   (iii)
   Catch-up contributions for individuals age 50 or over
   In the case of an individual who has attained the age of 50 before the close of the taxable year, the limitation under clause (i)(II) shall be increased by the applicable amount determined under
   section 219(b)(5)(B)(ii)
   (after the application of section 219(b)(5)(C)(iii)).
   (E)
   Eligible employer
   For purposes of this paragraph—
   (i)
   In general
   The term “
   eligible employer
   ” means any employer if the employer does not maintain a
   qualified plan
   with respect to which contributions are made, or benefits are accrued, for service in the year for which the determination is being made. If only individuals other than
   employees
   described in subparagraph (A) of
   section 410(b)(3)
   are eligible to participate in such arrangement, then the preceding sentence shall be applied without regard to any
   qualified plan
   in which only
   employees
   described in such subparagraph are eligible to participate.
   (ii)
   Relief for acquisitions, etc.
   Rules similar to the rules of
   section 408(p)(10)
   shall apply for purposes of clause (i).
   (iii)
   Qualified plan
   The term “
   qualified plan
   ” means a plan, contract, pension, account, or trust described in subparagraph (A) or (B) of paragraph (5) of
   section 219(g)
   (determined without regard to the last sentence of such paragraph (5)).
   (F)
   Eligible employee
   For purposes of this paragraph, the term “
   eligible employee
   ” means any
   employee
   of the employer other than an
   employee
   who is permitted to be excluded under paragraph (12)(A).
   (17)
   Special rules relating to hardship withdrawals
   For purposes of paragraphs (7) and (11)—
   (A)
   Amounts which may be withdrawn
   The following amounts may be distributed upon hardship of the
   employee
   :
   (i)
   Contributions made pursuant to a salary reduction agreement (within the meaning of
   section 3121(a)(5)(D)
   ).
   (ii)
   Qualified nonelective contributions (as defined in
   section 401(m)(4)(C)
   ).
   (iii)
   Qualified
   matching contributions
   described in section 401(k)(3)(D)(ii)(I).
   (iv)
   Earnings on any contributions described in clause (i), (ii), or (iii).
   (B)
   No requirement to take available loan
   A distribution shall not be treated as failing to be made upon the hardship of an
   employee
   solely because the
   employee
   does not take any available loan under the plan.
   (c)
   Taxability of beneficiary under nonqualified annuities or under annuities purchased by exempt organizations
   Premiums paid by an employer for an annuity contract which is not subject to subsection (a) shall be included in the gross income of the
   employee
   in accordance with section 83 (relating to property transferred in connection with performance of services), except that the value of such contract shall be substituted for the fair market value of the property for purposes of applying such section. The preceding sentence shall not apply to that portion of the premiums paid which is excluded from gross income under subsection (b). In the case of any portion of any contract which is attributable to premiums to which this subsection applies, the amount actually paid or made available under such contract to any beneficiary which is attributable to such premiums shall be taxable to the beneficiary (in the year in which so paid or made available) under section 72 (relating to annuities).
   (Aug. 16, 1954, ch. 736,
   68A Stat. 137
   ;
   Pub. L. 85–866, title I, § 23(a)
   –(c),
   Sept. 2, 1958
   ,
   72 Stat. 1620–1622
   ;
   Pub. L. 87–370, § 3(a)
   ,
   Oct. 4, 1961
   ,
   75 Stat. 801
   ;
   Pub. L. 87–792, § 4(d)
   ,
   Oct. 10, 1962
   ,
   76 Stat. 825
   ;
   Pub. L. 88–272, title II, § 232(e)(4)
   –(6),
   Feb. 26, 1964
   ,
   78 Stat. 111
   ;
   Pub. L. 91–172, title III, § 321(b)(2)
   , title V, § 515(a)(2),
   Dec. 30, 1969
   ,
   83 Stat. 591
   , 644;
   Pub. L. 93–406, title II
   , §§ 1022(e), 2002(g)(6), 2004(c)(4), 2005(b)(2),
   Sept. 2, 1974
   ,
   88 Stat. 940
   , 969, 986, 991;
   Pub. L. 94–267, § 1(b)
   ,
   Apr. 15, 1976
   ,
   90 Stat. 366
   ;
   Pub. L. 94–455, title XIV, § 1402(b)(1)(D)
   , (2), title XV, § 1504(a), title XIX, §§ 1901(a)(58), (b)(8)(A), 1906(b)(13)(A),
   Oct. 4, 1976
   ,
   90 Stat. 1731
   , 1732, 1738, 1774, 1794, 1834;
   Pub. L. 95–458, § 4(b)
   ,
   Oct. 14, 1978
   ,
   92 Stat. 1259
   ;
   Pub. L. 95–600, title I
   , §§ 154(a), 156(a), (b), 157(g)(2),
   Nov. 6, 1978
   ,
   92 Stat. 2801
   , 2802, 2808;
   Pub. L. 96–222, title I, § 101(a)(12)
   , (13)(C),
   Apr. 1, 1980
   ,
   94 Stat. 204
   ;
   Pub. L. 97–34, title III, § 311(b)(3)(B)
   ,
   Aug. 13, 1981
   ,
   95 Stat. 280
   ;
   Pub. L. 97–248, title II, § 251(a)
   , (b), (c)(3),
   Sept. 3, 1982
   ,
   96 Stat. 529–531
   ;
   Pub. L. 97–448, title I, § 103(c)(8)(B)
   ,
   Jan. 12, 1983
   ,
   96 Stat. 2377
   ;
   Pub. L. 98–21, title I, § 122(c)(4)
   ,
   Apr. 20, 1983
   ,
   97 Stat. 87
   ;
   Pub. L. 98–369, div. A, title IV, § 491(d)(12)
   , title V, §§ 521(c), 522(a)(2), (3), (d)(9)–(11), title X, § 1001(b)(4), (e),
   July 18, 1984
   ,
   98 Stat. 849
   , 867, 869–871, 1011, 1012;
   Pub. L. 99–514, title XI
   , §§ 1120(a), (b), 1122(b)(1)(B), (d), 1123(c), title XVIII, § 1852(a)(3)(A), (B), (5)(B), (b)(10),
   Oct. 22, 1986
   ,
   100 Stat. 2463
   , 2466, 2469, 2474, 2865, 2867;
   Pub. L. 100–647, title I, § 1011(c)(7)(B)
   , (12), (m)(1), (2), title VI, § 6052(a)(1),
   Nov. 10, 1988
   ,
   102 Stat. 3458
   , 3459, 3471, 3696;
   Pub. L. 101–508, title XI, § 11701(k)
   ,
   Nov. 5, 1990
   ,
   104 Stat. 1388–513
   ;
   Pub. L. 102–318, title V
   , §§ 521(b)(12), (13), 522(a)(3), (c)(2), (3),
   July 3, 1992
   ,
   106 Stat. 311
   , 314, 315;
   Pub. L. 104–188, title I
   , §§ 1450(c)(1), 1704(t)(69),
   Aug. 20, 1996
   ,
   110 Stat. 1815
   , 1891;
   Pub. L. 105–34, title XV
   , §§ 1504(a)(1), 1505(c), title XVI, § 1601(d)(6)(B),
   Aug. 5, 1997
   ,
   111 Stat. 1063
   , 1064, 1090;
   Pub. L. 105–206, title VI, § 6005(c)(2)(B)
   ,
   July 22, 1998
   ,
   112 Stat. 800
   ;
   Pub. L. 106–554, § 1(a)(7) [title III, § 314(e)(1)]
   ,
   Dec. 21, 2000
   ,
   114 Stat. 2763
   , 2763A–643;
   Pub. L. 107–16, title VI
   , §§ 632(a)(2), 641(b)(1), (e)(7), 642(b)(1), 646(a)(2), 647(a),
   June 7, 2001
   ,
   115 Stat. 113
   , 120, 121, 126, 127;
   Pub. L. 107–147, title IV, § 411(p)(1)
   –(3),
   Mar. 9, 2002
   ,
   116 Stat. 49
   , 50;
   Pub. L. 108–311, title IV
   , §§ 404(e), 408(a)(11),
   Oct. 4, 2004
   ,
   118 Stat. 1188
   , 1191;
   Pub. L. 109–135, title IV, § 412(w)
   ,
   Dec. 21, 2005
   ,
   119 Stat. 2638
   ;
   Pub. L. 109–280, title VIII
   , §§ 827(b)(2), (3), 829(a)(2), (3), 845(b)(1), (2),
   Aug. 17, 2006
   ,
   120 Stat. 1000
   , 1002, 1015;
   Pub. L. 110–245, title I, § 104(c)(2)
   ,
   June 17, 2008
   ,
   122 Stat. 1627
   ;
   Pub. L. 116–94, div. O, title I
   , §§ 109(c), 111(a),
   Dec. 20, 2019
   ,
   133 Stat. 3151
   , 3152;
   Pub. L. 117–328, div. T, title I
   , §§ 106(a), 110(e), 113(b), 121(b), 125(a)(2)(A), (B)(i), 128(a), (b), title III, §§ 312(b), 334(b)(2)–(4), title VI, § 602(a), (b),
   Dec. 29, 2022
   ,
   136 Stat. 5286
   , 5293, 5295, 5310, 5314, 5315, 5330, 5347, 5370, 5391.)
   [1]
   So in original. No cl. (ii) has been enacted.


-/
-- TODO: Add type definitions
-- TODO: Add main functions
-- TODO: Add theorems to prove