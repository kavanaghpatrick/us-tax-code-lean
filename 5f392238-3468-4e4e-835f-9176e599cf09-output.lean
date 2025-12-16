/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 5f392238-3468-4e4e-835f-9176e599cf09

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
# IRC Section 72 - Annuities; certain proceeds of endowment and life insurance contracts

This file formalizes IRC §72 (Annuities; certain proceeds of endowment and life insurance contracts).

## References
- [26 USC §72](https://www.law.cornell.edu/uscode/text/26/72)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 72 - Annuities; certain proceeds of endowment and life insurance contracts
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   General rules for annuities
   (1)
   Income inclusion
   Except as otherwise provided in this chapter, gross income includes any amount received as an annuity (whether for a period certain or during one or more lives) under an annuity, endowment, or life insurance contract.
   (2)
   Partial annuitization
   If any amount is received as an annuity for a period of 10 years or more or during one or more lives under any portion of an annuity, endowment, or life insurance contract—
   (A)
   such portion shall be treated as a separate contract for purposes of this section,
   (B)
   for purposes of applying subsections (b), (c), and (e), the investment in the contract shall be allocated pro rata between each portion of the contract from which amounts are received as an annuity and the portion of the contract from which amounts are not received as an annuity, and
   (C)
   a separate annuity starting date under subsection (c)(4) shall be determined with respect to each portion of the contract from which amounts are received as an annuity.
   (b)
   Exclusion ratio
   (1)
   In general
   Gross income does not include that part of any amount received as an annuity under an annuity, endowment, or life insurance contract which bears the same ratio to such amount as the investment in the contract (as of the annuity starting date) bears to the expected return under the contract (as of such date).
   (2)
   Exclusion limited to investment
   The portion of any amount received as an annuity which is excluded from gross income under paragraph (1) shall not exceed the unrecovered investment in the contract immediately before the receipt of such amount.
   (3)
   Deduction where annuity payments cease before entire investment recovered
   (A)
   In general
   If—
   (i)
   after the annuity starting date, payments as an annuity under the contract cease by reason of the death of an annuitant, and
   (ii)
   as of the date of such cessation, there is unrecovered investment in the contract,
   the amount of such unrecovered investment (in excess of any amount specified in subsection (e)(5) which was not included in gross income) shall be allowed as a deduction to the annuitant for his last taxable year.
   (B)
   Payments to other persons
   In the case of any contract which provides for payments meeting the requirements of subparagraphs (B) and (C) of subsection (c)(2), the deduction under subparagraph (A) shall be allowed to the person entitled to such payments for the taxable year in which such payments are received.
   (C)
   Net operating loss deductions provided
   For purposes of section 172, a deduction allowed under this paragraph shall be treated as if it were attributable to a trade or business of the taxpayer.
   (4)
   Unrecovered investment
   For purposes of this subsection, the unrecovered investment in the contract as of any date is—
   (A)
   the investment in the contract (determined without regard to subsection (c)(2)) as of the annuity starting date, reduced by
   (B)
   the aggregate amount received under the contract on or after such annuity starting date and before the date as of which the determination is being made, to the extent such amount was excludable from gross income under this subtitle.
   (c)
   Definitions
   (1)
   Investment in the contract
   For purposes of subsection (b), the investment in the contract as of the annuity starting date is—
   (A)
   the aggregate amount of premiums or other consideration paid for the contract, minus
   (B)
   the aggregate amount received under the contract before such date, to the extent that such amount was excludable from gross income under this subtitle or prior income tax laws.
   (2)
   Adjustment in investment where there is refund feature
   If—
   (A)
   the expected return under the contract depends in whole or in part on the life expectancy of one or more individuals;
   (B)
   the contract provides for payments to be made to a beneficiary (or to the estate of an annuitant) on or after the death of the annuitant or annuitants; and
   (C)
   such payments are in the nature of a
   refund of the consideration paid
   ,
   then the value (computed without discount for interest) of such payments on the annuity starting date shall be subtracted from the amount determined under paragraph (1). Such value shall be computed in accordance with actuarial tables prescribed by the Secretary. For purposes of this paragraph and of subsection (e)(2)(A), the term “
   refund of the consideration paid
   ” includes amounts payable after the death of an annuitant by reason of a provision in the contract for a life annuity with minimum period of payments certain, but (if part of the consideration was contributed by an employer) does not include that part of any payment to a beneficiary (or to the estate of the annuitant) which is not attributable to the consideration paid by the
   employee
   for the contract as determined under paragraph (1)(A).
   (3)
   Expected return
   For purposes of subsection (b), the expected return under the contract shall be determined as follows:
   (A)
   Life expectancy
   If the expected return under the contract, for the period on and after the annuity starting date, depends in whole or in part on the life expectancy of one or more individuals, the expected return shall be computed with reference to actuarial tables prescribed by the Secretary.
   (B)
   Installment payments
   If subparagraph (A) does not apply, the expected return is the aggregate of the amounts receivable under the contract as an annuity.
   (4)
   Annuity starting date
   For purposes of this section, the annuity starting date in the case of any contract is the first day of the first period for which an amount is received as an annuity under the contract.
   (d)
   Special rules for qualified employer retirement plans
   (1)
   Simplified method of taxing annuity payments
   (A)
   In general
   In the case of any amount received as an annuity under a
   qualified employer retirement plan
   —
   (i)
   subsection (b) shall not apply, and
   (ii)
   the investment in the contract shall be recovered as provided in this paragraph.
   (B)
   Method of recovering investment in contract
   (i)
   In general
   Gross income shall not include so much of any monthly annuity payment under a
   qualified employer retirement plan
   as does not exceed the amount obtained by dividing—
   (I)
   the investment in the contract (as of the annuity starting date), by
   (II)
   the number of anticipated payments determined under the table contained in clause (iii) (or, in the case of a contract to which subsection (c)(3)(B) applies, the number of monthly annuity payments under such contract).
   (ii)
   Certain rules made applicable
   Rules similar to the rules of paragraphs (2) and (3) of subsection (b) shall apply for purposes of this paragraph.
   (iii)
   Number of anticipated payments
   If the annuity is payable over the life of a single individual, the number of anticipated payments shall be determined as follows:
   If the age of the annuitant on the
   annuity starting date is:
   The number of anticipated payments is:
   Not more than 55
   360
   More than 55 but not more than 60
   310
   More than 60 but not more than 65
   260
   More than 65 but not more than 70
   210
   More than 70
   160.
   (iv)
   Number of anticipated payments where more than one life
   If the annuity is payable over the lives of more than 1 individual, the number of anticipated payments shall be determined as follows:
   If the combined ages of annuitants are:
   The number is:
   Not more than 110
   410
   More than 110 but not more than 120
   360
   More than 120 but not more than 130
   310
   More than 130 but not more than 140
   260
   More than 140
   210.
   (C)
   Adjustment for refund feature not applicable
   For purposes of this paragraph, investment in the contract shall be determined under subsection (c)(1) without regard to subsection (c)(2).
   (D)
   Special rule where lump sum paid in connection with commencement of annuity payments
   If, in connection with the commencement of annuity payments under any
   qualified employer retirement plan
   , the taxpayer receives a lump-sum payment—
   (i)
   such payment shall be taxable under subsection (e) as if received before the annuity starting date, and
   (ii)
   the investment in the contract for purposes of this paragraph shall be determined as if such payment had been so received.
   (E)
   Exception
   This paragraph shall not apply in any case where the
   primary annuitant
   has attained age 75 on the annuity starting date unless there are fewer than 5 years of guaranteed payments under the annuity.
   (F)
   Adjustment where annuity payments not on monthly basis
   In any case where the annuity payments are not made on a monthly basis, appropriate adjustments in the application of this paragraph shall be made to take into account the period on the basis of which such payments are made.
   (G)
   Qualified employer retirement plan
   For purposes of this paragraph, the term “
   qualified employer retirement plan
   ” means any plan or contract described in paragraph (1), (2), or (3) of section 4974(c).
   (2)
   Treatment of employee contributions under defined contribution plans
   For purposes of this section,
   employee
   contributions (and any income allocable thereto) under a defined contribution plan may be treated as a separate contract.
   (3)
   Treatment of contributions to a pension-linked emergency savings account
   For purposes of this section, contributions to a pension-linked emergency savings account to which
   section 402A(e)
   applies (and any income allocable thereto) may be treated as a separate contract.
   (e)
   Amounts not received as annuities
   (1)
   Application of subsection
   (A)
   In general
   This subsection shall apply to any amount which—
   (i)
   is received under an annuity, endowment, or life insurance contract, and
   (ii)
   is not received as an annuity,
   if no provision of this subtitle (other than this subsection) applies with respect to such amount.
   (B)
   Dividends
   For purposes of this section, any amount received which is in the nature of a dividend or similar distribution shall be treated as an amount not received as an annuity.
   (2)
   General rule
   Any amount to which this subsection applies—
   (A)
   if received on or after the annuity starting date, shall be included in gross income, or
   (B)
   if received before the annuity starting date—
   (i)
   shall be included in gross income to the extent allocable to
   income on the contract
   , and
   (ii)
   shall not be included in gross income to the extent allocable to the investment in the contract.
   (3)
   Allocation of amounts to income and investment
   For purposes of paragraph (2)(B)—
   (A)
   Allocation to income
   Any amount to which this subsection applies shall be treated as allocable to
   income on the contract
   to the extent that such amount does not exceed the excess (if any) of—
   (i)
   the cash value of the contract (determined without regard to any surrender charge) immediately before the amount is received, over
   (ii)
   the investment in the contract at such time.
   (B)
   Allocation to investment
   Any amount to which this subsection applies shall be treated as allocable to investment in the contract to the extent that such amount is not allocated to income under subparagraph (A).
   (4)
   Special rules for application of paragraph (2)(B)
   For purposes of paragraph (2)(B)—
   (A)
   Loans treated as distributions
   If, during any taxable year, an individual—
   (i)
   receives (directly or indirectly) any amount as a loan under any contract to which this subsection applies, or
   (ii)
   assigns or pledges (or agrees to assign or pledge) any portion of the value of any such contract,
   such amount or portion shall be treated as received under the contract as an amount not received as an annuity. The preceding sentence shall not apply for purposes of determining investment in the contract, except that the investment in the contract shall be increased by any amount included in gross income by reason of the amount treated as received under the preceding sentence.
   (B)
   Treatment of policyholder dividends
   Any amount described in paragraph (1)(B) shall not be included in gross income under paragraph (2)(B)(i) to the extent such amount is retained by the insurer as a premium or other consideration paid for the contract.
   (C)
   Treatment of transfers without adequate consideration
   (i)
   In general
   If an individual who holds an annuity contract transfers it without full and adequate consideration, such individual shall be treated as receiving an amount equal to the excess of—
   (I)
   the cash surrender value of such contract at the time of transfer, over
   (II)
   the investment in such contract at such time,
   under the contract as an amount not received as an annuity.
   (ii)
   Exception for certain transfers between spouses or former spouses
   Clause (i) shall not apply to any transfer to which section 1041(a) (relating to transfers of property between spouses or incident to divorce) applies.
   (iii)
   Adjustment to investment in contract of transferee
   If under clause (i) an amount is included in the gross income of the transferor of an annuity contract, the investment in the contract of the
   transferee
   in such contract shall be increased by the amount so included.
   (5)
   Retention of existing rules in certain cases
   (A)
   In general
   In any case to which this paragraph applies—
   (i)
   paragraphs (2)(B) and (4)(A) shall not apply, and
   (ii)
   if paragraph (2)(A) does not apply,
   the amount shall be included in gross income, but only to the extent it exceeds the investment in the contract.
   (B)
   Existing contracts
   This paragraph shall apply to contracts entered into before
   August 14, 1982
   . Any amount allocable to investment in the contract after
   August 13, 1982
   , shall be treated as from a contract entered into after such date.
   (C)
   Certain life insurance and endowment contracts
   Except as provided in paragraph (10) and except to the extent prescribed by the Secretary by regulations, this paragraph shall apply to any amount not received as an annuity which is received under a life insurance or
   endowment contract
   .
   (D)
   Contracts under qualified plans
   Except as provided in paragraph (8), this paragraph shall apply to any amount received—
   (i)
   from a trust described in
   section 401(a)
   which is exempt from tax under section 501(a),
   (ii)
   from a contract—
   (I)
   purchased by a trust described in clause (i),
   (II)
   purchased as part of a plan described in section 403(a),
   (III)
   described in section 403(b), or
   (IV)
   provided for
   employees
   of a life insurance company under a plan described in section 818(a)(3), or
   (iii)
   from an individual retirement account or an individual retirement annuity.
   Any dividend described in
   section 404(k)
   which is received by a participant or beneficiary shall, for purposes of this subparagraph, be treated as paid under a separate contract to which clause (ii)(I) applies.
   (E)
   Full refunds, surrenders, redemptions, and maturities
   This paragraph shall apply to—
   (i)
   any amount received, whether in a single sum or otherwise, under a contract in full discharge of the obligation under the contract which is in the nature of a
   refund of the consideration paid
   for the contract, and
   (ii)
   any amount received under a contract on its complete surrender, redemption, or maturity.
   In the case of any amount to which the preceding sentence applies, the rule of paragraph (2)(A) shall not apply.
   (6)
   Investment in the contract
   For purposes of this subsection, the investment in the contract as of any date is—
   (A)
   the aggregate amount of premiums or other consideration paid for the contract before such date, minus
   (B)
   the aggregate amount received under the contract before such date, to the extent that such amount was excludable from gross income under this subtitle or prior income tax laws.
   [(7)
   Repealed.
   Pub. L. 100–647, title I, § 1011A(b)(9)(A)
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3474
   ]
   (8)
   Extension of paragraph (2)(b)
   [1]
   to qualified plans
   (A)
   In general
   Notwithstanding any other provision of this subsection, in the case of any amount received before the annuity starting date from a trust or contract described in paragraph (5)(D), paragraph (2)(B) shall apply to such amounts.
   (B)
   Allocation of amount received
   For purposes of paragraph (2)(B), the amount allocated to the investment in the contract shall be the portion of the amount described in subparagraph (A) which bears the same ratio to such amount as the investment in the contract bears to the account balance. The determination under the preceding sentence shall be made as of the time of the distribution or at such other time as the Secretary may prescribe.
   (C)
   Treatment of forfeitable rights
   If an
   employee
   does not have a nonforfeitable right to any amount under any trust or contract to which subparagraph (A) applies, such amount shall not be treated as part of the account balance.
   (D)
   Investment in the contract before 1987
   In the case of a plan which on
   May 5, 1986
   , permitted withdrawal of any
   employee
   contributions before separation from service, subparagraph (A) shall apply only to the extent that amounts received before the annuity starting date (when increased by amounts previously received under the contract after
   December 31, 1986
   ) exceed the investment in the contract as of
   December 31, 1986
   .
   (9)
   Extension of paragraph (2)(B) to qualified tuition programs and Coverdell education savings accounts
   Notwithstanding any other provision of this subsection, paragraph (2)(B) shall apply to amounts received under a qualified tuition program (as defined in
   section 529(b)
   ) or under a Coverdell education savings account (as defined in section 530(b)). The rule of paragraph (8)(B) shall apply for purposes of this paragraph.
   (10)
   Treatment of modified endowment contracts
   (A)
   In general
   Notwithstanding paragraph (5)(C), in the case of any modified
   endowment contract
   (as defined in
   section 7702A
   )—
   (i)
   paragraphs (2)(B) and (4)(A) shall apply, and
   (ii)
   in applying paragraph (4)(A), “any person” shall be substituted for “an individual”.
   (B)
   Treatment of certain burial contracts
   Notwithstanding subparagraph (A), paragraph (4)(A) shall not apply to any assignment (or pledge) of a modified
   endowment contract
   if such assignment (or pledge) is solely to cover the payment of expenses referred to in section 7702(e)(2)(C)(iii) and if the maximum death benefit under such contract does not exceed $25,000.
   (11)
   Special rules for certain combination contracts providing long-term care insurance
   Notwithstanding paragraphs (2), (5)(C), and (10), in the case of any charge against the cash value of an annuity contract or the cash surrender value of a life insurance contract made as payment for coverage under a qualified long-term care insurance contract which is part of or a rider on such annuity or life insurance contract—
   (A)
   the investment in the contract shall be reduced (but not below zero) by such charge, and
   (B)
   such charge shall not be includible in gross income.
   (12)
   Anti-abuse rules
   (A)
   In general
   For purposes of determining the amount includible in gross income under this subsection—
   (i)
   all modified
   endowment contracts
   issued by the same company to the same policyholder during any calendar year shall be treated as 1 modified
   endowment contract
   , and
   (ii)
   all annuity contracts issued by the same company to the same policyholder during any calendar year shall be treated as 1 annuity contract.
   The preceding sentence shall not apply to any contract described in paragraph (5)(D).
   (B)
   Regulatory authority
   The Secretary may by regulations prescribe such additional rules as may be necessary or appropriate to prevent avoidance of the purposes of this subsection through serial purchases of contracts or otherwise.
   (f)
   Special rules for computing employees’ contributions
   In computing, for purposes of subsection (c)(1)(A), the aggregate amount of premiums or other consideration paid for the contract, and for purposes of subsection (e)(6), the aggregate premiums or other consideration paid, amounts contributed by the employer shall be included, but only to the extent that—
   (1)
   such amounts were includible in the gross income of the
   employee
   under this subtitle or prior income tax laws; or
   (2)
   if such amounts had been paid directly to the
   employee
   at the time they were contributed, they would not have been includible in the gross income of the
   employee
   under the law applicable at the time of such contribution.
   Paragraph (2) shall not apply to amounts which were contributed by the employer after
   December 31, 1962
   , and which would not have been includible in the gross income of the
   employee
   by reason of the application of
   section 911
   if such amounts had been paid directly to the
   employee
   at the time of contribution. The preceding sentence shall not apply to amounts which were contributed by the employer, as determined under regulations prescribed by the Secretary, to provide pension or annuity credits, to the extent such credits are attributable to services performed before
   January 1, 1963
   , and are provided pursuant to pension or annuity plan provisions in existence on
   March 12, 1962
   , and on that date applicable to such services, or to the extent such credits are attributable to services performed as a foreign missionary (within the meaning of section 403(b)(2)(D)(iii), as in effect before the enactment of the
   Economic Growth and Tax Relief Reconciliation Act of 2001
   ).
   (g)
   Rules for transferee where transfer was for value
   Where any contract (or any interest therein) is transferred (by assignment or otherwise) for a valuable consideration, to the extent that the contract (or interest therein) does not, in the hands of the
   transferee
   , have a basis which is determined by reference to the basis in the hands of the transferor, then—
   (1)
   for purposes of this section, only the actual value of such consideration, plus the amount of the premiums and other consideration paid by the
   transferee
   after the transfer, shall be taken into account in computing the aggregate amount of the premiums or other consideration paid for the contract;
   (2)
   for purposes of subsection (c)(1)(B), there shall be taken into account only the aggregate amount received under the contract by the
   transferee
   before the annuity starting date, to the extent that such amount was excludable from gross income under this subtitle or prior income tax laws; and
   (3)
   the annuity starting date is the first day of the first period for which the
   transferee
   received an amount under the contract as an annuity.
   For purposes of this subsection, the term “
   transferee
   ” includes a beneficiary of, or the estate of, the
   transferee
   .
   (h)
   Option to receive annuity in lieu of lump sum
   If—
   (1)
   a contract provides for payment of a lump sum in full discharge of an obligation under the contract, subject to an option to receive an annuity in lieu of such lump sum;
   (2)
   the option is exercised within 60 days after the day on which such lump sum first became payable; and
   (3)
   part or all of such lump sum would (but for this subsection) be includible in gross income by reason of subsection (e)(1),
   then, for purposes of this subtitle, no part of such lump sum shall be considered as includible in gross income at the time such lump sum first became payable.
   [(i)
   Repealed.
   Pub. L. 94–455, title XIX, § 1951(b)(1)(A)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1836
   ]
   (j)
   Interest
   Notwithstanding any other provision of this section, if any amount is held under an agreement to pay interest thereon, the interest payments shall be included in gross income.
   [(k)
   Repealed.
   Pub. L. 98–369, div. A, title IV, § 421(b)(1)
   ,
   July 18, 1984
   ,
   98 Stat. 794
   ]
   (l)
   Face-amount certificates
   For purposes of this section, the term “
   endowment contract
   ” includes a face-amount certificate, as defined in section 2(a)(15) of the
   Investment Company Act of 1940
   (15 U.S.C., sec.
   80a–2
   ), issued after
   December 31, 1954
   .
   (m)
   Special rules applicable to employee annuities and distributions under employee plans
   [(1)
   Repealed.
   Pub. L. 93–406, title II, § 2001(h)(2)
   ,
   Sept. 2, 1974
   ,
   88 Stat. 957
   ]
   (2)
   Computation of consideration paid by the employee
   In computing—
   (A)
   the aggregate amount of premiums or other consideration paid for the contract for purposes of subsection (c)(1)(A) (relating to the investment in the contract), and
   (B)
   the aggregate premiums or other consideration paid for purposes of subsection (e)(6) (relating to certain amounts not received as an annuity),
   any amount allowed as a deduction with respect to the contract under section 404 which was paid while the
   employee
   was an
   employee
   within the meaning of section 401(c)(1) shall be treated as consideration contributed by the employer, and there shall not be taken into account any portion of the premiums or other consideration for the contract paid while the
   employee
   was an
   owner-employee
   which is properly allocable (as determined under regulations prescribed by the Secretary) to the cost of life, accident, health, or other insurance.
   (3)
   Life insurance contracts
   (A)
   This paragraph shall apply to any life insurance contract—
   (i)
   purchased as a part of a plan described in section 403(a), or
   (ii)
   purchased by a trust described in
   section 401(a)
   which is exempt from tax under section 501(a) if the proceeds of such contract are payable directly or indirectly to a participant in such trust or to a beneficiary of such participant.
   (B)
   Any contribution to a plan described in subparagraph (A)(i) or a trust described in subparagraph (A)(ii) which is allowed as a deduction under section 404, and any income of a trust described in subparagraph (A)(ii), which is determined in accordance with regulations prescribed by the Secretary to have been applied to purchase the life insurance protection under a contract described in subparagraph (A), is includible in the gross income of the participant for the taxable year when so applied.
   (C)
   In the case of the death of an individual insured under a contract described in subparagraph (A), an amount equal to the cash surrender value of the contract immediately before the death of the insured shall be treated as a payment under such plan or a distribution by such trust, and the excess of the amount payable by reason of the death of the insured over such cash surrender value shall not be includible in gross income under this section and shall be treated as provided in section 101.
   [(4)
   Repealed.
   Pub. L. 97–248, title II, § 236(b)(1)
   ,
   Sept. 3, 1982
   ,
   96 Stat. 510
   ]
   (5)
   Penalties applicable to certain amounts received by 5-percent owners
   (A)
   This paragraph applies to amounts which are received from a qualified trust described in
   section 401(a)
   or under a plan described in section 403(a) at any time by an individual who is, or has been, a
   5-percent owner,
   or by a successor of such an individual, but only to the extent such amounts are determined, under regulations prescribed by the Secretary, to exceed the benefits provided for such individual under the plan formula.
   (B)
   If a person receives an amount to which this paragraph applies, his tax under this chapter for the taxable year in which such amount is received shall be increased by an amount equal to 10 percent of the portion of the amount so received which is includible in his gross income for such taxable year.
   (C)
   For purposes of this paragraph, the term “
   5-percent owner
   ” means any individual who, at any time during the 5 plan years preceding the plan year ending in the taxable year in which the amount is received, is a
   5-percent owner
   (as defined in
   section 416(i)(1)(B)
   ).
   (6)
   Owner-employee defined
   For purposes of this subsection, the term “
   owner-employee
   ” has the meaning assigned to it by section 401(c)(3) and includes an individual for whose benefit an individual retirement account or annuity described in section 408(a) or (b) is maintained. For purposes of the preceding sentence, the term “
   owner-employee
   ” shall include an
   employee
   within the meaning of section 401(c)(1).
   (7)
   Meaning of disabled
   For purposes of this section, an individual shall be considered to be disabled if he is unable to engage in any substantial gainful activity by reason of any medically determinable physical or mental impairment which can be expected to result in death or to be of long-continued and indefinite duration. An individual shall not be considered to be disabled unless he furnishes proof of the existence thereof in such form and manner as the Secretary may require.
   [(8)
   Repealed.
   Pub. L. 97–248, title II, § 236(b)(1)
   ,
   Sept. 3, 1982
   ,
   96 Stat. 510
   ]
   [(9)
   Repealed.
   Pub. L. 98–369, div. A, title VII, § 713(d)(1)
   ,
   July 18, 1984
   ,
   98 Stat. 957
   ]

-- [Content truncated - key provisions above]

-- TODO: Add type definitions
-- TODO: Add main functions
-- TODO: Add theorems to prove