/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b293de86-2b89-4352-8d45-ab90f5b3e6a3

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
# IRC Section 415 - Limitations on benefits and contribution under qualified plans

This file formalizes IRC §415 (Limitations on benefits and contribution under qualified plans).

## References
- [26 USC §415](https://www.law.cornell.edu/uscode/text/26/415)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 415 - Limitations on benefits and contribution under qualified plans
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   (1)
   Trusts
   A trust which is a part of a pension, profitsharing, or stock bonus plan shall not constitute a qualified trust under
   section 401(a)
   if—
   (A)
   in the case of a
   defined benefit plan
   , the plan provides for the payment of benefits with respect to a participant which exceed the limitation of subsection (b), or
   (B)
   in the case of a
   defined contribution plan
   , contributions and other additions under the plan with respect to any participant for any taxable year exceed the limitation of subsection (c).
   (2)
   Section applies to certain annuities and accounts
   In the case of—
   (A)
   an employee annuity plan described in section 403(a),
   (B)
   an annuity contract described in section 403(b), or
   (C)
   a simplified employee pension described in section 408(k),
   such a contract, plan, or pension shall not be considered to be described in section 403(a), 403(b), or 408(k), as the case may be, unless it satisfies the requirements of subparagraph (A) or subparagraph (B) of paragraph (1), whichever is appropriate, and has not been disqualified under subsection (g). In the case of an annuity contract described in section 403(b), the preceding sentence shall apply only to the portion of the annuity contract which exceeds the limitation of subsection (b) or the limitation of subsection (c), whichever is appropriate.
   (b)
   Limitation for defined benefit plans
   (1)
   In general
   Benefits with respect to a participant exceed the limitation of this subsection if, when expressed as an
   annual benefit
   (within the meaning of paragraph (2)), such
   annual benefit
   is greater than the lesser of—
   (A)
   $160,000, or
   (B)
   100 percent of the participant’s average compensation for his high 3 years.
   (2)
   Annual benefit
   (A)
   In general
   For purposes of paragraph (1), the term “
   annual benefit
   ” means a benefit payable annually in the form of a straight life annuity (with no ancillary benefits) under a plan to which employees do not contribute and under which no rollover contributions (as defined in sections
   402(c)
   ,
   403(a)(4)
   ,
   403(b)(8)
   ,
   408(d)(3)
   , and
   457(e)(16)
   ) are made.
   (B)
   Adjustment for certain other forms of benefit
   If the benefit under the plan is payable in any form other than the form described in subparagraph (A), or if the employees contribute to the plan or make rollover contributions (as defined in sections
   402(c)
   ,
   403(a)(4)
   ,
   403(b)(8)
   ,
   408(d)(3)
   , and
   457(e)(16)
   ), the determinations as to whether the limitation described in paragraph (1) has been satisfied shall be made, in accordance with regulations prescribed by the Secretary by adjusting such benefit so that it is equivalent to the benefit described in subparagraph (A). For purposes of this subparagraph, any ancillary benefit which is not directly related to retirement income benefits shall not be taken into account; and that portion of any joint and survivor annuity which constitutes a qualified joint and survivor annuity (as defined in section 417) shall not be taken into account.
   (C)
   Adjustment to $160,000 limit where benefit begins before age 62
   If the retirement income benefit under the plan begins before age 62, the determination as to whether the $160,000 limitation set forth in paragraph (1)(A) has been satisfied shall be made, in accordance with regulations prescribed by the Secretary, by reducing the limitation of paragraph (1)(A) so that such limitation (as so reduced) equals an
   annual benefit
   (beginning when such retirement income benefit begins) which is equivalent to a $160,000
   annual benefit
   beginning at age 62.
   (D)
   Adjustment to $160,000 limit where benefit begins after age 65
   If the retirement income benefit under the plan begins after age 65, the determination as to whether the $160,000 limitation set forth in paragraph (1)(A) has been satisfied shall be made, in accordance with regulations prescribed by the Secretary, by increasing the limitation of paragraph (1)(A) so that such limitation (as so increased) equals an
   annual benefit
   (beginning when such retirement income benefit begins) which is equivalent to a $160,000
   annual benefit
   beginning at age 65.
   (E)
   Limitation on certain assumptions
   (i)
   For purposes of adjusting any limitation under subparagraph (C) and, except as provided in clause (ii), for purposes of adjusting any benefit under subparagraph (B), the interest rate assumption shall not be less than the greater of 5 percent or the rate specified in the plan.
   (ii)
   For purposes of adjusting any benefit under subparagraph (B) for any form of benefit subject to section 417(e)(3), the interest rate assumption shall not be less than the greatest of—
   (I)
   5.5 percent,
   (II)
   the rate that provides a benefit of not more than 105 percent of the benefit that would be provided if the
   applicable interest rate
   (as defined in
   section 417(e)(3)
   ) were the interest rate assumption, or
   (III)
   the rate specified under the plan.
   (iii)
   For purposes of adjusting any limitation under subparagraph (D), the interest rate assumption shall not be greater than the lesser of 5 percent or the rate specified in the plan.
   (iv)
   For purposes of this subsection, no adjustments under subsection (d)(1) shall be taken into account before the year for which such adjustment first takes effect.
   (v)
   For purposes of adjusting any benefit or limitation under subparagraph (B), (C), or (D), the mortality table used shall be the
   applicable mortality table
   (within the meaning of
   section 417(e)(3)(B)
   ).
   (vi)
   In the case of a plan maintained by an eligible employer (as defined in
   section 408(p)(2)(C)(i)
   ), clause (ii) shall be applied without regard to subclause (II) thereof.
   [(F)
   Repealed.
   Pub. L. 107–16, title VI, § 611(a)(5)(A)
   ,
   June 7, 2001
   ,
   115 Stat. 97
   ]
   (G)
   Special limitation for qualified police or firefighters
   In the case of a
   qualified participant
   , subparagraph (C) of this paragraph shall not apply.
   (H)
   Qualified participant defined
   For purposes of subparagraph (G), the term “
   qualified participant
   ” means a participant—
   (i)
   in a
   defined benefit plan
   which is maintained by a State, Indian tribal government (as defined in
   section 7701(a)(40)
   ), or any political subdivision thereof,
   (ii)
   with respect to whom the period of service taken into account in determining the amount of the benefit under such
   defined benefit plan
   includes at least 15 years of service of the participant—
   (I)
   as a full-time employee of any police department or fire department which is organized and operated by the State, Indian tribal government (as so defined), or any political subdivision maintaining such
   defined benefit plan
   to provide police protection, firefighting services, or emergency medical services for any area within the jurisdiction of such State, Indian tribal government (as so defined), or any political subdivision, or
   (II)
   as a member of the Armed Forces of the United States.
   (I)
   Exemption for survivor and disability benefits provided under governmental plans
   Subparagraph (C) of this paragraph and paragraph (5) shall not apply to—
   (i)
   income received from a
   governmental plan
   (as defined in section 414(d)) as a pension, annuity, or similar allowance as the result of the recipient becoming disabled by reason of personal injuries or sickness, or
   (ii)
   amounts received from a
   governmental plan
   by the beneficiaries, survivors, or the estate of an employee as the result of the death of the employee.
   (3)
   Average compensation for high 3 years
   For purposes of paragraph (1), a participant’s high 3 years shall be the period of consecutive calendar years (not more than 3) during which the participant had the greatest aggregate compensation from the employer. In the case of an employee within the meaning of section 401(c)(1), the preceding sentence shall be applied by substituting for “compensation from the employer” the following: “the participant’s
   earned income
   (within the meaning of
   section 401(c)(2)
   but determined without regard to any exclusion under section 911)”.
   (4)
   Total annual benefits not in excess of $10,000
   Notwithstanding the preceding provisions of this subsection, the benefits payable with respect to a participant under any
   defined benefit plan
   shall be deemed not to exceed the limitation of this subsection if—
   (A)
   the retirement benefits payable with respect to such participant under such plan and under all other
   defined benefit plans
   of the employer do not exceed $10,000 for the plan year, or for any prior plan year, and
   (B)
   the employer has not at any time maintained a
   defined contribution plan
   in which the participant participated.
   (5)
   Reduction for participation or service of less than 10 years
   (A)
   Dollar limitation
   In the case of an employee who has less than 10 years of participation in a
   defined benefit plan
   , the limitation referred to in paragraph (1)(A) shall be the limitation determined under such paragraph (without regard to this paragraph) multiplied by a fraction—
   (i)
   the numerator of which is the number of years (or part thereof) of participation in the
   defined benefit plan
   of the employer, and
   (ii)
   the denominator of which is 10.
   (B)
   Compensation and benefits limitations
   The provisions of subparagraph (A) shall apply to the limitations under paragraphs (1)(B) and (4), except that such subparagraph shall be applied with respect to years of service with an employer rather than years of participation in a plan.
   (C)
   Limitation on reduction
   In no event shall subparagraph (A) or (B) reduce the limitations referred to in paragraphs (1) and (4) to an amount less than ⅒ of such limitation (determined without regard to this paragraph).
   (D)
   Application to changes in benefit structure
   To the extent provided in regulations, subparagraph (A) shall be applied separately with respect to each change in the benefit structure of a plan.
   (6)
   Computation of benefits and contributions
   The computation of—
   (A)
   benefits under a
   defined contribution plan
   , for purposes of section 401(a)(4),
   (B)
   contributions made on behalf of a participant in a
   defined benefit plan
   , for purposes of section 401(a)(4), and
   (C)
   contributions and benefits provided for a participant in a plan described in section 414(k), for purposes of this section
   shall not be made on a basis inconsistent with regulations prescribed by the Secretary.
   (7)
   Benefits under certain collectively bargained plans
   For a year, the limitation referred to in paragraph (1)(B) shall not apply to benefits with respect to a participant under a
   defined benefit plan
   (other than a
   multiemployer plan)
   —
   (A)
   which is maintained for such year pursuant to a collective bargaining agreement between employee representatives and one or more employers,
   (B)
   which, at all times during such year, has at least 100 participants,
   (C)
   under which benefits are determined solely by reference to length of service, the particular years during which service was rendered, age at retirement, and date of retirement,
   (D)
   which provides that an employee who has at least 4 years of service has a nonforfeitable right to 100 percent of his accrued benefit derived from employer contributions, and
   (E)
   which requires, as a condition of participation in the plan, that an employee complete a period of not more than 60 consecutive days of service with the employer or employers maintaining the plan.
   This paragraph shall not apply to a participant whose compensation for any 3 years during the 10-year period immediately preceding the year in which he separates from service exceeded the average compensation for such 3 years of all participants in such plan. This paragraph shall not apply to a participant for any period for which he is a participant under another plan to which this section applies which is maintained by an employer maintaining this plan. For any year for which the paragraph applies to benefits with respect to a participant, paragraph (1)(A) and subsection (d)(1)(A) shall be applied with respect to such participant by substituting one-half the amount otherwise applicable for such year under paragraph (1)(A) for “$160,000”.
   (8)
   Social security retirement age defined
   For purposes of this subsection, the term “
   social security retirement age
   ” means the age used as the retirement age under section 216(
   l
   ) of the
   Social Security Act
   , except that such section shall be applied—
   (A)
   without regard to the age increase factor, and
   (B)
   as if the early retirement age under section 216(l)(2) of such Act were 62.
   (9)
   Special rule for commercial airline pilots
   (A)
   In general
   Except as provided in subparagraph (B), in the case of any participant who is a commercial airline pilot, if, as of the time of the participant’s retirement, regulations prescribed by the
   Federal Aviation Administration
   require an individual to separate from service as a commercial airline pilot after attaining any age occurring on or after age 60 and before age 62, paragraph (2)(C) shall be applied by substituting such age for age 62.
   (B)
   Individuals who separate from service before age 60
   If a participant described in subparagraph (A) separates from service before age 60, the rules of paragraph (2)(C) shall apply.
   (10)
   Special rule for State, Indian tribal, and local government plans
   (A)
   Limitation to equal accrued benefit
   In the case of a plan maintained for its employees by any State or political subdivision thereof, or by any agency or instrumentality of the foregoing, or a
   governmental plan
   described in the last sentence of section 414(d) (relating to plans of Indian tribal governments), the limitation with respect to a
   qualified participant
   under this subsection shall not be less than the accrued benefit of the participant under the plan (determined without regard to any amendment of the plan made after
   October 14, 1987
   ).
   (B)
   Qualified participant
   For purposes of this paragraph, the term “
   qualified participant
   ” means a participant who first became a participant in the plan maintained by the employer before
   January 1, 1990
   .
   (C)
   Election
   (i)
   In general
   This paragraph shall not apply to any plan unless each employer maintaining the plan elects before the close of the 1st plan year beginning after
   December 31, 1989
   , to have this subsection (other than paragraph (2)(G)).
   (ii)
   Revocation of election
   An election under clause (i) may be revoked not later than the last day of the third plan year beginning after the date of the enactment of this clause. The revocation shall apply to all plan years to which the election applied and to all subsequent plan years. Any amount paid by a plan in a taxable year ending after the revocation shall be includible in income in such taxable year under the rules of this chapter in effect for such taxable year, except that, for purposes of applying the limitations imposed by this section, any portion of such amount which is attributable to any taxable year during which the election was in effect shall be treated as received in such taxable year.
   (11)
   Special limitation rule for governmental and multiemployer plans
   In the case of a
   governmental plan
   (as defined in section 414(d)) or a
   multiemployer plan
   (as defined in section 414(f)), subparagraph (B) of paragraph (1) shall not apply. Subparagraph (B) of paragraph (1) shall not apply to a plan maintained by an organization described in section 3121(w)(3)(A) except with respect to
   highly compensated benefits
   . For purposes of this paragraph, the term “
   highly compensated benefits
   ” means any benefits accrued for an employee in any year on or after the first year in which such employee is a
   highly compensated employee
   (as defined in section 414(q)) of the organization described in section 3121(w)(3)(A). For purposes of applying paragraph (1)(B) to
   highly compensated benefits
   , all benefits of the employee otherwise taken into account (without regard to this paragraph) shall be taken into account.
   (12)
   Special rule for certain employees of rural electric cooperatives
   (A)
   In general
   Subparagraph (B) of paragraph (1) shall not apply to a participant in an
   eligible rural electric cooperative plan
   , except in the case of a participant who was a
   highly compensated employee
   (as defined in section 414(q)) of an employer maintaining such plan for the earlier of—
   (i)
   the plan year in which the participant terminated employment with such employer, or
   (ii)
   the plan year in which distributions commence under the plan with respect to the participant, or
   for any of the 5 plan years immediately preceding such earlier plan year.
   (B)
   Eligible rural electric cooperative plan
   For purposes of this paragraph—
   (i)
   In general
   The term “
   eligible rural electric cooperative plan
   ” means a plan maintained by more than 1 employer, with respect to which at least 85 percent of the employers maintaining the plan are rural cooperatives described in clause (i) or (ii) of
   section 401(k)(7)(B)
   or are a national association of such a rural cooperative.
   (ii)
   Election
   An employer maintaining an eligible rural cooperative plan may elect not to have subparagraph (A) apply to its employees.
   (C)
   Regulations
   The Secretary shall prescribe such regulations and other guidance as are necessary to limit the application of subparagraph (A) such that it does not result in increased benefits for
   highly compensated employees
   .
   (c)
   Limitation for defined contribution plans
   (1)
   In general
   Contributions and other additions with respect to a participant exceed the limitation of this subsection if, when expressed as an
   annual addition
   (within the meaning of paragraph (2)) to the participant’s account, such
   annual addition
   is greater than the lesser of—
   (A)
   $40,000, or
   (B)
   100 percent of the
   participant’s compensation
   .
   (2)
   Annual addition
   For purposes of paragraph (1), the term “
   annual addition
   ” means the sum of any year of—
   (A)
   employer contributions,
   (B)
   the employee contributions, and
   (C)
   forfeitures.
   For the purposes of this paragraph, employee contributions under subparagraph (B) are determined without regard to any rollover contributions (as defined in sections
   402(c)
   ,
   403(a)(4)
   ,
   403(b)(8)
   ,
   408(d)(3)
   , and
   457(e)(16)
   ) without regard to employee contributions to a simplified employee pension which are excludable from gross income under section 408(k)(6). Subparagraph (B) of paragraph (1) shall not apply to any contribution for medical benefits (within the meaning of section 419A(f)(2)) after separation from service which is treated as an
   annual addition.
   (3)
   Participant’s compensation
   For purposes of paragraph (1)—
   (A)
   In general
   The term “
   participant’s compensation
   ” means the compensation of the participant from the employer for the year.
   (B)
   Special rule for self-employed individuals
   In the case of an employee within the meaning of section 401(c)(1), subparagraph (A) shall be applied by substituting “the participant’s
   earned income
   (within the meaning of section 401(c)(2) but determined without regard to any exclusion under section 911)” for “compensation of the participant from the employer”.
   (C)
   Special rules for permanent and total disability
   In the case of a participant in any
   defined contribution plan
   —
   (i)
   who is permanently and totally disabled (as defined in
   section 22(e)(3)
   ),
   (ii)
   who is not a
   highly compensated employee
   (within the meaning of
   section 414(q)
   ), and
   (iii)
   with respect to whom the employer elects, at such time and in such manner as the Secretary may prescribe, to have this subparagraph apply,
   the term “
   participant’s compensation
   ” means the compensation the participant would have received for the year if the participant was paid at the rate of compensation paid immediately before becoming permanently and totally disabled. This subparagraph shall apply only if contributions made with respect to amounts treated as compensation under this subparagraph are nonforfeitable when made. If a
   defined contribution plan
   provides for the continuation of contributions on behalf of all participants described in clause (i) for a fixed or determinable period, this subparagraph shall be applied without regard to clauses (ii) and (iii).
   (D)
   Certain deferrals included
   The term “
   participant’s compensation
   ” shall include—
   (i)
   any
   elective deferral
   (as defined in
   section 402(g)(3)
   ), and
   (ii)
   any amount which is contributed or deferred by the employer at the election of the employee and which is not includible in the gross income of the employee by reason of section 125, 132(f)(4), or 457.
   (E)
   Annuity contracts
   In the case of an annuity contract described in section 403(b), the term “
   participant’s compensation
   ” means the participant’s includible compensation determined under section 403(b)(3).
   [(4)
   Repealed.
   Pub. L. 107–16, title VI, § 632(a)(3)(E)
   ,
   June 7, 2001
   ,
   115 Stat. 114
   ]
   [(5)
   Repealed.
   Pub. L. 97–248, title II, § 238(d)(5)
   ,
   Sept. 3, 1982
   ,
   96 Stat. 513
   ]
   (6)
   Special rule for employee stock ownership plans
   If no more than one-third of the employer contributions to an employee stock ownership plan (as described in
   section 4975(e)(7)
   ) for a year which are deductible under paragraph (9) of section 404(a) are allocated to
   highly compensated employees
   (within the meaning of section 414(q)), the limitations imposed by this section shall not apply to—
   (A)
   forfeitures of employer securities (within the meaning of
   section 409
   ) under such an employee stock ownership plan if such securities were acquired with the proceeds of a loan (as described in section 404(a)(9)(A)), or
   (B)
   employer contributions to such an employee stock ownership plan which are deductible under section 404(a)(9)(B) and charged against the participant’s account.
   The amount of any qualified gratuitous transfer (as defined in
   section 664(g)(1)
   ) allocated to a participant for any limitation year shall not exceed the limitations imposed by this section, but such amount shall not be taken into account in determining whether any other amount exceeds the limitations imposed by this section.
   (7)
   Special rules relating to church plans
   (A)
   Alternative contribution limitation
   (i)
   In general
   Notwithstanding any other provision of this subsection, at the election of a participant who is an employee of a
   church
   or a
   convention or association of churches
   , including an organization described in section 414(e)(3)(B)(ii), contributions and other additions for an annuity contract or retirement income account described in
   section 403(b)
   with respect to such participant, when expressed as an
   annual addition
   to such participant’s account, shall be treated as not exceeding the limitation of paragraph (1) if such
   annual addition
   is not in excess of $10,000.
   (ii)
   $40,000 aggregate limitation
   The total amount of additions with respect to any participant which may be taken into account for purposes of this subparagraph for all years may not exceed $40,000.
   (B)
   Number of years of service for duly ordained, commissioned, or licensed ministers or lay employees
   For purposes of this paragraph—
   (i)
   all years of service by—
   (I)
   a duly ordained, commissioned, or licensed minister of a
   church
   , or
   (II)
   a lay person,
   as an employee of a
   church
   , a
   convention or association of churches
   , including an organization described in section 414(e)(3)(B)(ii), shall be considered as years of service for 1 employer, and
   (ii)
   all amounts contributed for annuity contracts by each such
   church
   (or
   convention or association of churches
   ) or such organization during such years for such minister or lay person shall be considered to have been contributed by 1 employer.
   (C)
   Foreign missionaries
   In the case of any individual described in subparagraph (B) performing services outside the United States, contributions and other additions for an annuity contract or retirement income account described in
   section 403(b)
   with respect to such employee, when expressed as an
   annual addition
   to such employee’s account, shall not be treated as exceeding the limitation of paragraph (1) if such
   annual addition
   is not in excess of $3,000. This subparagraph shall not apply with respect to any taxable year to any individual whose adjusted gross income for such taxable year (determined separately and without regard to community property laws) exceeds $17,000.
   (D)
   Annual addition
   For purposes of this paragraph, the term “
   annual addition
   ” has the meaning given such term by paragraph (2).
   (E)
   Church, convention or association of churches
   For purposes of this paragraph, the terms “
   church
   ” and “
   convention or association of churches
   ” have the same meaning as when used in section 414(e).
   (8)
   Special rule for difficulty of care payments excluded from gross income
   (A)
   In general
   For purposes of paragraph (1)(B), in the case of an individual who for a taxable year excludes from gross income under
   section 131
   a qualified foster care payment which is a difficulty of care payment, the
   participant’s compensation,
   or
   earned income,
   as the case may be, shall be increased by the amount so excluded.
   (B)
   Contributions allocable to difficulty of care payments treated as after-tax
   Any contribution by the participant which is allowable due to such increase—
   (i)
   shall be treated for purposes of this title as investment in the contract, and
   (ii)
   shall not cause a plan (and any arrangement which is part of such plan) to be treated as failing to meet any requirements of this chapter solely by reason of allowing any such contributions.
   (d)
   Cost-of-living adjustments
   (1)
   In general
   The Secretary shall adjust annually—
   (A)
   the $160,000 amount in subsection (b)(1)(A),
   (B)
   in the case of a participant who is separated from service, the amount taken into account under subsection (b)(1)(B), and
   (C)
   the $40,000 amount in subsection (c)(1)(A),
   for increases in the cost-of-living in accordance with regulations prescribed by the Secretary.
   (2)
   Method
   The regulations prescribed under paragraph (1) shall provide for—
   (A)
   an adjustment with respect to any calendar year based on the increase in the applicable index for the calendar quarter ending September 30 of the preceding calendar year over such index for the base period, and
   (B)
   adjustment procedures which are similar to the procedures used to adjust benefit amounts under section 215(i)(2)(A) of the
   Social Security Act
   .
   (3)
   Base period
   For purposes of paragraph (2)—
   (A)
   $160,000 amount
   The base period taken into account for purposes of paragraph (1)(A) is the calendar quarter beginning
   July 1, 2001
   .
   (B)
   Separations after
   December 31, 1994
   The base period taken into account for purposes of paragraph (1)(B) with respect to individuals separating from service with the employer after
   December 31, 1994
   , is the calendar quarter beginning July 1 of the calendar year preceding the calendar year in which such separation occurs.
   (C)
   Separations before
   January 1, 1995
   The base period taken into account for purposes of paragraph (1)(B) with respect to individuals separating from service with the employer before
   January 1, 1995
   , is the calendar quarter beginning October 1 of the calendar year preceding the calendar year in which such separation occurs.
   (D)
   $40,000 amount
   The base period taken into account for purposes of paragraph (1)(C) is the calendar quarter beginning
   July 1, 2001
   .

-- [Content truncated - key provisions above]

-- TODO: Add type definitions
-- TODO: Add main functions
-- TODO: Add theorems to prove