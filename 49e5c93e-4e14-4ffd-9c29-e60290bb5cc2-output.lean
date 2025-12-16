/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 49e5c93e-4e14-4ffd-9c29-e60290bb5cc2

Aristotle encountered an error processing this file. The team has been notified.

-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bf419631-8bf6-4d7f-8e0a-ad5ab950ae71

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
# IRC Section 402 - Taxability of beneficiary of employees’ trust

This file formalizes IRC §402 (Taxability of beneficiary of employees’ trust).

## References
- [26 USC §402](https://www.law.cornell.edu/uscode/text/26/402)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 402 - Taxability of beneficiary of employees’ trust
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Taxability of beneficiary of exempt trust
   Except as otherwise provided in this section, any amount actually distributed to any distributee by any
   employees
   ’ trust described in section 401(a) which is exempt from tax under section 501(a) shall be taxable to the distributee, in the taxable year of the distributee in which distributed, under section 72 (relating to annuities).
   (b)
   Taxability of beneficiary of nonexempt trust
   (1)
   Contributions
   Contributions to an
   employees
   ’ trust made by an employer during a taxable year of the employer which ends with or within a taxable year of the trust for which the trust is not exempt from tax under section 501(a) shall be included in the gross income of the
   employee
   in accordance with section 83 (relating to property transferred in connection with performance of services), except that the value of the
   employee
   ’s interest in the trust shall be substituted for the fair market value of the property for purposes of applying such section.
   (2)
   Distributions
   The amount actually distributed or made available to any distributee by any trust described in paragraph (1) shall be taxable to the distributee, in the taxable year in which so distributed or made available, under section 72 (relating to annuities), except that distributions of income of such trust before the annuity starting date (as defined in section 72(c)(4)) shall be included in the gross income of the
   employee
   without regard to section 72(e)(5) (relating to amounts not received as annuities).
   (3)
   Grantor trusts
   A beneficiary of any trust described in paragraph (1) shall not be considered the owner of any portion of such trust under subpart E of part I of subchapter J (relating to grantors and others treated as substantial owners).
   (4)
   Failure to meet requirements of section 410(b)
   (A)
   Highly compensated employees
   If 1 of the reasons a trust is not exempt from tax under section 501(a) is the failure of the plan of which it is a part to meet the requirements of section 401(a)(26) or 410(b), then a
   highly compensated employee
   shall, in lieu of the amount determined under paragraph (1) or (2) include in gross income for the taxable year with or within which the taxable year of the trust ends an amount equal to the vested accrued benefit of such
   employee
   (other than the
   employee’
   s investment in the contract) as of the close of such taxable year of the trust.
   (B)
   Failure to meet coverage tests
   If a trust is not exempt from tax under
   section 501(a)
   for any taxable year solely because such trust is part of a plan which fails to meet the requirements of section 401(a)(26) or 410(b), paragraphs (1) and (2) shall not apply by reason of such failure to any
   employee
   who was not a
   highly compensated employee
   during—
   (i)
   such taxable year, or
   (ii)
   any preceding period for which service was creditable to such
   employee
   under the plan.
   (C)
   Highly compensated employee
   For purposes of this paragraph, the term “
   highly compensated employee
   ” has the meaning given such term by section 414(q).
   (c)
   Rules applicable to rollovers from exempt trusts
   (1)
   Exclusion from income
   If—
   (A)
   any portion of the balance to the credit of an
   employee
   in a
   qualified trust
   is paid to the
   employee
   in an
   eligible rollover distribution
   ,
   (B)
   the distributee transfers any portion of the property received in such distribution to an
   eligible retirement plan
   , and
   (C)
   in the case of a distribution of property other than money, the amount so transferred consists of the property distributed,
   then such distribution (to the extent so transferred) shall not be includible in gross income for the taxable year in which paid.
   (2)
   Maximum amount which may be rolled over
   In the case of any
   eligible rollover distribution
   , the maximum amount transferred to which paragraph (1) applies shall not exceed the portion of such distribution which is includible in gross income (determined without regard to paragraph (1)). The preceding sentence shall not apply to such distribution to the extent—
   (A)
   such portion is transferred in a direct trustee-to-trustee transfer to a
   qualified trust
   or to an annuity contract described in section 403(b) and such trust or contract provides for separate accounting for amounts so transferred (and earnings thereon), including separately accounting for the portion of such distribution which is includible in gross income and the portion of such distribution which is not so includible, or
   (B)
   such portion is transferred to an
   eligible retirement plan
   described in clause (i) or (ii) of paragraph (8)(B).
   In the case of a transfer described in subparagraph (A) or (B), the amount transferred shall be treated as consisting first of the portion of such distribution that is includible in gross income (determined without regard to paragraph (1)).
   (3)
   Time limit on transfers
   (A)
   In general
   Except as provided in subparagraphs (B) and (C), paragraph (1) shall not apply to any transfer of a distribution made after the 60th day following the day on which the distributee received the property distributed.
   (B)
   Hardship exception
   The Secretary may waive the 60-day requirement under subparagraph (A) where the failure to waive such requirement would be against equity or good conscience, including casualty, disaster, or other events beyond the reasonable control of the individual subject to such requirement.
   (C)
   Rollover of certain plan loan offset amounts
   (i)
   In general
   In the case of a
   qualified plan loan offset amount
   , paragraph (1) shall not apply to any transfer of such amount made after the due date (including extensions) for filing the return of tax for the taxable year in which such amount is treated as distributed from a
   qualified employer plan.
   (ii)
   Qualified plan loan offset amount
   For purposes of this subparagraph, the term “
   qualified plan loan offset amount
   ” means a
   plan loan offset amount
   which is treated as distributed from a
   qualified employer plan
   to a participant or beneficiary solely by reason of—
   (I)
   the termination of the
   qualified employer plan
   , or
   (II)
   the failure to meet the repayment terms of the loan from such plan because of the severance from employment of the participant.
   (iii)
   Plan loan offset amount
   For purposes of clause (ii), the term “
   plan loan offset amount
   ” means the amount by which the participant’s accrued benefit under the plan is reduced in order to repay a loan from the plan.
   (iv)
   Limitation
   This subparagraph shall not apply to any
   plan loan offset amount
   unless such
   plan loan offset amount
   relates to a loan to which
   section 72(p)(1)
   does not apply by reason of section 72(p)(2).
   (v)
   Qualified employer plan
   For purposes of this subsection, the term “
   qualified employer plan
   ” has the meaning given such term by section 72(p)(4).
   (4)
   Eligible rollover distribution
   For purposes of this subsection, the term “
   eligible rollover distribution
   ” means any distribution to an
   employee
   of all or any portion of the balance to the credit of the
   employee
   in a
   qualified trust;
   except that such term shall not include—
   (A)
   any distribution which is one of a series of substantially equal periodic payments (not less frequently than annually) made—
   (i)
   for the life (or life expectancy) of the
   employee
   or the joint lives (or joint life expectancies) of the
   employee
   and the
   employee
   ’s designated beneficiary, or
   (ii)
   for a specified period of 10 years or more,
   (B)
   any distribution to the extent such distribution is required under section 401(a)(9), and
   (C)
   any distribution which is made upon hardship of the
   employee
   .
   If all or any portion of a distribution during 2020 is treated as an
   eligible rollover distribution
   but would not be so treated if the minimum distribution requirements under
   section 401(a)(9)
   had applied during 2020, such distribution shall not be treated as an
   eligible rollover distribution
   for purposes of section 401(a)(31) or 3405(c) or subsection (f) of this section.
   (5)
   Transfer treated as rollover contribution under section 408
   For purposes of this title, a transfer to an
   eligible retirement plan
   described in clause (i) or (ii) of paragraph (8)(B) resulting in any portion of a distribution being excluded from gross income under paragraph (1) shall be treated as a rollover contribution described in section 408(d)(3).
   (6)
   Sales of distributed property
   For purposes of this subsection—
   (A)
   Transfer of proceeds from sale of distributed property treated as transfer of distributed property
   The transfer of an amount equal to any portion of the proceeds from the sale of property received in the distribution shall be treated as the transfer of property received in the distribution.
   (B)
   Proceeds attributable to increase in value
   The excess of fair market value of property on sale over its fair market value on distribution shall be treated as property received in the distribution.
   (C)
   Designation where amount of distribution exceeds rollover contribution
   In any case where part or all of the distribution consists of property other than money—
   (i)
   the portion of the money or other property which is to be treated as attributable to amounts not included in gross income, and
   (ii)
   the portion of the money or other property which is to be treated as included in the rollover contribution,
   shall be determined on a ratable basis unless the taxpayer designates otherwise. Any designation under this subparagraph for a taxable year shall be made not later than the time prescribed by law for filing the return for such taxable year (including extensions thereof). Any such designation, once made, shall be irrevocable.
   (D)
   Nonrecognition of gain or loss
   No gain or loss shall be recognized on any sale described in subparagraph (A) to the extent that an amount equal to the proceeds is transferred pursuant to paragraph (1).
   (7)
   Special rule for frozen deposits
   (A)
   In general
   The 60-day period described in paragraph (3) shall not—
   (i)
   include any period during which the amount transferred to the
   employee
   is a
   frozen deposit
   , or
   (ii)
   end earlier than 10 days after such amount ceases to be a
   frozen deposit
   .
   (B)
   Frozen deposits
   For purposes of this subparagraph, the term “
   frozen deposit
   ” means any deposit which may not be withdrawn because of—
   (i)
   the bankruptcy or insolvency of any financial institution, or
   (ii)
   any requirement imposed by the State in which such institution is located by reason of the bankruptcy or insolvency (or threat thereof) of 1 or more financial institutions in such State.
   A deposit shall not be treated as a
   frozen deposit
   unless on at least 1 day during the 60-day period described in paragraph (3) (without regard to this paragraph) such deposit is described in the preceding sentence.
   (8)
   Definitions
   For purposes of this subsection—
   (A)
   Qualified trust
   The term “
   qualified trust
   ” means an
   employees’
   trust described in
   section 401(a)
   which is exempt from tax under section 501(a).
   (B)
   Eligible retirement plan
   The term “
   eligible retirement plan
   ” means—
   (i)
   an individual retirement account described in section 408(a),
   (ii)
   an individual retirement annuity described in
   section 408(b)
   (other than an endowment contract),
   (iii)
   a
   qualified trust
   ,
   (iv)
   an annuity plan described in section 403(a),
   (v)
   an eligible deferred compensation plan described in
   section 457(b)
   which is maintained by an eligible employer described in section 457(e)(1)(A), and
   (vi)
   an annuity contract described in section 403(b).
   If any portion of an
   eligible rollover distribution
   is attributable to payments or distributions from a designated Roth account (as defined in
   section 402A
   ), an
   eligible retirement plan
   with respect to such portion shall include only another designated Roth account and a
   Roth IRA.
   (9)
   Rollover where spouse receives distribution after death of employee
   If any distribution attributable to an
   employee
   is paid to the spouse of the
   employee
   after the
   employee
   ’s death, the preceding provisions of this subsection shall apply to such distribution in the same manner as if the spouse were the
   employee
   .
   (10)
   Separate accounting
   Unless a plan described in clause (v) of paragraph (8)(B) agrees to separately account for amounts rolled into such plan from
   eligible retirement plans
   not described in such clause, the plan described in such clause may not accept transfers or rollovers from such retirement plans.
   (11)
   Distributions to inherited individual retirement plan of nonspouse beneficiary
   (A)
   In general
   If, with respect to any portion of a distribution from an
   eligible retirement plan
   described in paragraph (8)(B)(iii) of a deceased
   employee,
   a direct trustee-to-trustee transfer is made to an individual retirement plan described in clause (i) or (ii) of paragraph (8)(B) established for the purposes of receiving the distribution on behalf of an individual who is a designated beneficiary (as defined by section 401(a)(9)(E)) of the
   employee
   and who is not the surviving spouse of the
   employee—
   (i)
   the transfer shall be treated as an
   eligible rollover distribution
   ,
   (ii)
   the individual retirement plan shall be treated as an inherited individual retirement account or individual retirement annuity (within the meaning of
   section 408(d)(3)(C)
   ) for purposes of this title, and
   (iii)
   section 401(a)(9)(B)
   (other than clause (iv) thereof) shall apply to such plan.
   (B)
   Certain trusts treated as beneficiaries
   For purposes of this paragraph, to the extent provided in rules prescribed by the Secretary, a trust maintained for the benefit of one or more designated beneficiaries shall be treated in the same manner as a designated beneficiary.
   (12)
   In the case of an inadvertent benefit overpayment from a plan to which
   section 414(aa)(1)
   applies that is transferred to an
   eligible retirement plan
   by or on behalf of a participant or beneficiary—
   (A)
   the portion of such overpayment with respect to which recoupment is not sought on behalf of the plan shall be treated as having been paid in an
   eligible rollover distribution
   if the payment would have been an
   eligible rollover distribution
   but for being an overpayment, and
   (B)
   the portion of such overpayment with respect to which recoupment is sought on behalf of the plan shall be permitted to be returned to such plan and in such case shall be treated as an
   eligible rollover distribution
   transferred to such plan by the participant or beneficiary who received such overpayment (and the plans making and receiving such transfer shall be treated as permitting such transfer).
   (13)
   Recontributions of withdrawals for home purchases
   (A)
   General rule
   (i)
   In general
   Any individual who received a
   qualified distribution
   may, during the
   applicable period,
   make one or more contributions in an aggregate amount not to exceed the amount of such
   qualified distribution
   to an
   eligible retirement plan
   (as defined in paragraph (8)(B)) of which such individual is a beneficiary and to which a rollover contribution of such distribution could be made under subsection (c) or section 403(a)(4), 403(b)(8), or 408(d)(3), as the case may be.
   (ii)
   Treatment of repayments
   Rules similar to the rules of clauses (ii) and (iii) of
   section 72(t)(11)(C)
   shall apply for purposes of this subsection.
   (B)
   Qualified distribution
   For purposes of this paragraph, the term “
   qualified distribution
   ” means any distribution—
   (i)
   described in section 401(k)(2)(B)(i)(IV), 403(b)(7)(A)(i)(V), or 403(b)(11)(B),
   (ii)
   which was to be used to purchase or construct a principal residence in a
   qualified disaster area
   , but which was not so used on account of the
   qualified disaster
   with respect to such area, and
   (iii)
   which was received during the period beginning on the date which is 180 days before the first day of the
   incident period
   of such
   qualified disaster
   and ending on the date which is 30 days after the last day of such
   incident period.
   (C)
   Definitions
   For purposes of this paragraph—
   (i)
   the terms “
   qualified disaster
   ”, “
   qualified disaster area
   ”, and
   “incident period”
   have the meaning given such terms under section 72(t)(11), and
   (ii)
   the term “
   applicable period
   ” has the meaning given such term under section 72(t)(8)(F).
   (d)
   Taxability of beneficiary of certain foreign situs trusts
   For purposes of subsections (a), (b), and (c), a stock bonus, pension, or profit-sharing trust which would qualify for exemption from tax under
   section 501(a)
   except for the fact that it is a trust created or organized outside the United States shall be treated as if it were a trust exempt from tax under section 501(a).
   (e)
   Other rules applicable to exempt trusts
   (1)
   Alternate payees
   (A)
   Alternate payee treated as distributee
   For purposes of subsection (a) and section 72, an alternate payee who is the spouse or former spouse of the participant shall be treated as the distributee of any distribution or payment made to the alternate payee under a qualified domestic relations order (as defined in
   section 414(p)
   ).
   (B)
   Rollovers
   If any amount is paid or distributed to an alternate payee who is the spouse or former spouse of the participant by reason of any qualified domestic relations order (within the meaning of
   section 414(p)
   ), subsection (c) shall apply to such distribution in the same manner as if such alternate payee were the
   employee.
   (2)
   Distributions by United States to nonresident aliens
   The amount includible under subsection (a) in the gross income of a nonresident alien with respect to a distribution made by the United States in respect of services performed by an
   employee
   of the United States shall not exceed an amount which bears the same ratio to the amount includible in gross income without regard to this paragraph as—
   (A)
   the aggregate
   basic pay
   paid by the United States to such
   employee
   for such services, reduced by the amount of such
   basic pay
   which was not includible in gross income by reason of being from sources without the United States, bears to
   (B)
   the aggregate
   basic pay
   paid by the United States to such
   employee
   for such services.
   In the case of distributions under the civil service retirement laws, the term “
   basic pay
   ” shall have the meaning provided in
   section 8331(3) of title 5
   , United States Code.
   (3)
   Cash or deferred arrangements
   For purposes of this title, contributions made by an employer on behalf of an
   employee
   to a trust which is a part of a qualified cash or deferred arrangement (as defined in
   section 401(k)(2)
   ) or which is part of a salary reduction agreement under section 403(b) shall not be treated as distributed or made available to the
   employee
   nor as contributions made to the trust by the
   employee
   merely because the arrangement includes provisions under which the
   employee
   has an election whether the contribution will be made to the trust or received by the
   employee
   in cash.
   (4)
   Net unrealized appreciation
   (A)
   Amounts attributable to employee contributions
   For purposes of subsection (a) and section 72, in the case of a distribution other than a lump sum distribution, the amount actually distributed to any distributee from a trust described in subsection (a) shall not include any net unrealized appreciation in
   securities of the employer corporation
   attributable to amounts contributed by the
   employee
   (other than deductible
   employee
   contributions within the meaning of
   section 72(o)(5)
   ). This subparagraph shall not apply to a distribution to which subsection (c) applies.
   (B)
   Amounts attributable to employer contributions
   For purposes of subsection (a) and section 72, in the case of any lump sum distribution which includes
   securities of the employer corporation
   , there shall be excluded from gross income the net unrealized appreciation attributable to that part of the distribution which consists of
   securities of the employer corporation
   . In accordance with rules prescribed by the Secretary, a taxpayer may elect, on the return of tax on which a lump sum distribution is required to be included, not to have this subparagraph apply to such distribution.
   (C)
   Determination of amounts and adjustments
   For purposes of subparagraphs (A) and (B), net unrealized appreciation and the resulting adjustments to basis shall be determined in accordance with regulations prescribed by the Secretary.
   (D)
   Lump-sum distribution
   For purposes of this paragraph—
   (i)
   In general
   The term “
   lump-sum distribution
   ” means the distribution or payment within one taxable year of the recipient of the balance to the credit of an
   employee
   which becomes payable to the recipient—
   (I)
   on account of the
   employee
   ’s death,
   (II)
   after the
   employee
   attains age 59½,
   (III)
   on account of the
   employee
   ’s separation from service, or
   (IV)
   after the
   employee
   has become disabled (within the meaning of
   section 72(m)(7)
   ),
   from a trust which forms a part of a plan described in section 401(a) and which is exempt from tax under section 501 or from a plan described in section 403(a). Subclause (III) of this clause shall be applied only with respect to an individual who is an
   employee
   without regard to section 401(c)(1), and subclause (IV) shall be applied only with respect to an
   employee
   within the meaning of section 401(c)(1). For purposes of this clause, a distribution to two or more trusts shall be treated as a distribution to one recipient. For purposes of this paragraph, the balance to the credit of the
   employee
   does not include the accumulated deductible
   employee
   contributions under the plan (within the meaning of section 72(
   o
   )(5)).
   (ii)
   Aggregation of certain trusts and plans
   For purposes of determining the balance to the credit of an
   employee
   under clause (i)—
   (I)
   all trusts which are part of a plan shall be treated as a single trust, all pension plans maintained by the employer shall be treated as a single plan, all profit-sharing plans maintained by the employer shall be treated as a single plan, and all stock bonus plans maintained by the employer shall be treated as a single plan, and
   (II)
   trusts which are not
   qualified trusts
   under section 401(a) and annuity contracts which do not satisfy the requirements of section 404(a)(2) shall not be taken into account.
   (iii)
   Community property laws
   The provisions of this paragraph shall be applied without regard to community property laws.
   (iv)
   Amounts subject to penalty
   This paragraph shall not apply to amounts described in subparagraph (A) of
   section 72(m)(5)
   to the extent that section 72(m)(5) applies to such amounts.
   (v)
   Balance to credit of employee not to include amounts payable under qualified domestic relations order
   For purposes of this paragraph, the balance to the credit of an
   employee
   shall not include any amount payable to an alternate payee under a qualified domestic relations order (within the meaning of
   section 414(p)
   ).
   (vi)
   Transfers to cost-of-living arrangement not treated as distribution
   For purposes of this paragraph, the balance to the credit of an
   employee
   under a
   defined contribution plan
   shall not include any amount transferred from such
   defined contribution plan
   to a qualified cost-of-living arrangement (within the meaning of
   section 415(k)(2)
   ) under a
   defined benefit plan.
   (vii)
   Lump-sum distributions of alternate payees
   If any distribution or payment of the balance to the credit of an
   employee
   would be treated as a
   lump-sum distribution
   , then, for purposes of this paragraph, the payment under a qualified domestic relations order (within the meaning of section 414(p)) of the balance to the credit of an alternate payee who is the spouse or former spouse of the
   employee
   shall be treated as a
   lump-sum distribution
   . For purposes of this clause, the balance to the credit of the alternate payee shall not include any amount payable to the
   employee.
   (E)
   Definitions relating to securities
   For purposes of this paragraph—
   (i)
   Securities
   The term “
   securities
   ” means only shares of stock and bonds or debentures issued by a corporation with interest coupons or in registered form.
   (ii)
   Securities of the employer
   The term “
   securities of the employer corporation
   ” includes
   securities
   of a parent or subsidiary corporation (as defined in subsections (e) and (f) of section 424) of the employer corporation.
   [(5)
   Repealed.
   Pub. L. 104–188, title I, § 1401(b)(13)
   ,
   Aug. 20, 1996
   ,
   110 Stat. 1789
   ]

-- TODO: Add type definitions
-- TODO: Add main functions