/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 79f029b3-c4b9-4ce8-af61-ebc664b62186

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
# IRC Section 414 - Definitions and special rules

This file formalizes IRC §414 (Definitions and special rules).

## References
- [26 USC §414](https://www.law.cornell.edu/uscode/text/26/414)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 414 - Definitions and special rules
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   Service for predecessor employer
   For purposes of this part—
   (1)
   in any case in which the employer maintains a plan of a predecessor employer, service for such predecessor shall be treated as service for the employer, and
   (2)
   in any case in which the employer maintains a plan which is not the plan maintained by a predecessor employer, service for such predecessor shall, to the extent provided in regulations prescribed by the Secretary, be treated as service for the employer.
   (b)
   Employees of controlled group of corporations
   (1)
   In general
   For purposes of sections 401, 408(k), 408(p), 410, 411, 415, and 416, all employees of all corporations which are members of a
   controlled group
   of corporations (within the meaning of section 1563(a), determined without regard to section 1563(a)(4) and (e)(3)(C)) shall be treated as employed by a single employer. With respect to a plan adopted by more than one such corporation, the applicable limitations provided by section 404(a) shall be determined as if all such employers were a single employer, and allocated to each employer in accordance with regulations prescribed by the Secretary.
   (2)
   Special rules for applying family attribution
   For purposes of applying the attribution rules under
   section 1563
   with respect to paragraph (1), the following rules apply:
   (A)
   Community property laws shall be disregarded for purposes of determining ownership.
   (B)
   Except as provided by the Secretary, stock of an individual not attributed under section 1563(e)(5) to such individual’s spouse shall not be attributed to such spouse by reason of the combined application of paragraphs (1) and (6)(A) of section 1563(e).
   (C)
   Except as provided by the Secretary, in the case of stock in different corporations that is attributed to a child under section 1563(e)(6)(A) from each parent, and is not attributed to such parents as spouses under section 1563(e)(5), such attribution to the child shall not by itself result in such corporations being members of the same
   controlled group
   .
   (3)
   Plan shall not fail to be treated as satisfying this section
   If application of paragraph (2) causes 2 or more entities to be a
   controlled group
   or to no longer be in a
   controlled group
   , such change shall be treated as a transaction to which
   section 410(b)(6)(C)
   applies.
   (c)
   Employees of partnerships, proprietorships, etc., which are under common control
   (1)
   In general
   Except as provided in paragraph (2), for purposes of sections 401, 408(k), 408(p), 410, 411, 415, and 416, under regulations prescribed by the Secretary, all employees of trades or businesses (whether or not incorporated) which are under common control shall be treated as employed by a single employer. The regulations prescribed under this subsection shall be based on principles similar to the principles which apply in the case of subsection (b).
   (2)
   Special rules relating to church plans
   (A)
   General rule
   Except as provided in subparagraphs (B) and (C), for purposes of this subsection and subsection (m), an
   organization
   that is otherwise eligible to participate in a
   church plan
   shall not be aggregated with another such
   organization
   and treated as a single employer with such other
   organization
   for a plan year beginning in a taxable year unless—
   (i)
   one such
   organization
   provides (directly or indirectly) at least 80 percent of the operating funds for the other
   organization
   during the preceding taxable year of the recipient
   organization
   , and
   (ii)
   there is a degree of common management or supervision between the
   organizations
   such that the
   organization
   providing the operating funds is directly involved in the day-to-day operations of the other
   organization
   .
   (B)
   Nonqualified church-controlled organizations
   Notwithstanding subparagraph (A), for purposes of this subsection and subsection (m), an
   organization
   that is a
   nonqualified church-controlled organization
   shall be aggregated with 1 or more other
   nonqualified church-controlled organizations
   , or with an
   organization
   that is not exempt from tax under section 501, and treated as a single employer with such other
   organization,
   if at least 80 percent of the directors or trustees of such other
   organization
   are either representatives of, or directly or indirectly controlled by, such
   nonqualified church-controlled organization
   . For purposes of this subparagraph, the term “
   nonqualified church-controlled organization
   ” means a church-controlled tax-exempt
   organization
   described in
   section 501(c)(3)
   that is not a qualified church-controlled
   organization
   (as defined in section 3121(w)(3)(B)).
   (C)
   Permissive aggregation among church-related organizations
   The
   church or convention or association of churches
   with which an
   organization
   described in subparagraph (A) is associated (within the meaning of subsection (e)(3)(D)), or an
   organization
   designated by such
   church or convention or association of churches
   , may elect to treat such
   organizations
   as a single employer for a plan year. Such election, once made, shall apply to all succeeding plan years unless revoked with notice provided to the Secretary in such manner as the Secretary shall prescribe.
   (D)
   Permissive disaggregation of church-related organizations
   For purposes of subparagraph (A), in the case of a
   church plan
   , an employer may elect to treat churches (as defined in
   section 403(b)(12)(B)
   ) separately from entities that are not churches (as so defined), without regard to whether such entities maintain separate
   church plans.
   Such election, once made, shall apply to all succeeding plan years unless revoked with notice provided to the Secretary in such manner as the Secretary shall prescribe.
   (d)
   Governmental plan
   For purposes of this part, the term “
   governmental plan
   ” means a plan established and maintained for its employees by the Government of the United States, by the government of any State or political subdivision thereof, or by any agency or instrumentality of any of the foregoing. The term “
   governmental plan
   ” also includes any plan to which the
   Railroad Retirement Act of 1935
   or 1937 applies and which is financed by contributions required under that Act and any plan of an international
   organization
   which is exempt from taxation by reason of the
   International Organizations Immunities Act
   (
   59 Stat. 669
   ). The term
   “governmental plan”
   includes a plan which is established and maintained by an Indian
   tribal
   government (as defined in section 7701(a)(40)), a subdivision of an Indian
   tribal
   government (determined in accordance with section 7871(d)), or an agency or instrumentality of either, and all of the participants of which are employees of such entity substantially all of whose services as such an employee are in the performance of essential governmental functions but not in the performance of commercial activities (whether or not an essential government function).
   (e)
   Church plan
   (1)
   In general
   For purposes of this part, the term “
   church plan
   ” means a plan established and maintained (to the extent required in paragraph (2)(B)) for its employees (or their benefici­aries) by a church or by a convention or association of churches which is exempt from tax under section 501.
   (2)
   Certain plans excluded
   The term “
   church plan
   ” does not include a plan—
   (A)
   which is established and maintained primarily for the benefit of employees (or their beneficiaries) of such
   church or convention or association of churches
   who are employed in connection with one or more unrelated trades or businesses (within the meaning of
   section 513
   ); or
   (B)
   if less than substantially all of the individuals included in the plan are individuals described in paragraph (1) or (3)(B) (or their beneficiaries).
   (3)
   Definitions and other provisions
   For purposes of this subsection—
   (A)
   Treatment as church plan
   A plan established and maintained for its employees (or their beneficiaries) by a church or by a convention or association of churches includes a plan maintained by an
   organization
   , whether a civil law corporation or otherwise, the principal purpose or function of which is the administration or funding of a plan or program for the provision of retirement benefits or welfare benefits, or both, for the employees of a church or a convention or association of churches, if such
   organization
   is controlled by or associated with a church or a convention or association of churches.
   (B)
   Employee defined
   The term employee of a church or a convention or association of churches shall include—
   (i)
   a duly ordained, commissioned, or licensed minister of a church in the exercise of his ministry, regardless of the source of his
   compensation
   ;
   (ii)
   an employee of an
   organization
   , whether a civil law corporation or otherwise, which is exempt from tax under section 501 and which is controlled by or associated with a church or a convention or association of churches; and
   (iii)
   an individual described in subparagraph (E).
   (C)
   Church treated as employer
   A church or a convention or association of churches which is exempt from tax under
   section 501
   shall be deemed the employer of any individual included as an employee under subparagraph (B).
   (D)
   Association with church
   An
   organization
   , whether a civil law corporation or otherwise, is associated with a church or a convention or association of churches if it shares common religious bonds and convictions with that
   church or convention or association of churches
   .
   (E)
   Special rule in case of separation from plan
   If an employee who is included in a
   church plan
   separates from the service of a church or a convention or association of churches or an
   organization
   described in clause (ii) of paragraph (3)(B), the
   church plan
   shall not fail to meet the requirements of this subsection merely because the plan—
   (i)
   retains the employee’s
   accrued benefit
   or account for the payment of benefits to the employee or his beneficiaries pursuant to the terms of the plan; or
   (ii)
   receives contributions on the employee’s behalf after the employee’s separation from such service, but only for a period of 5 years after such separation, unless the employee is disabled (within the meaning of the disability provisions of the
   church plan
   or, if there are no such provisions in the
   church plan
   , within the meaning of
   section 72(m)(7)
   ) at the time of such separation from service.
   (4)
   Correction of failure to meet church plan requirements
   (A)
   In general
   If a plan established and maintained for its employees (or their beneficiaries) by a church or by a convention or association of churches which is exempt from tax under section 501 fails to meet one or more of the requirements of this subsection and corrects its failure to meet such requirements within the
   correction period
   , the plan shall be deemed to meet the requirements of this subsection for the year in which the correction was made and for all prior years.
   (B)
   Failure to correct
   If a correction is not made within the
   correction period
   , the plan shall be deemed not to meet the requirements of this subsection beginning with the date on which the earliest failure to meet one or more of such requirements occurred.
   (C)
   Correction period defined
   The term “
   correction period
   ” means—
   (i)
   the period, ending 270 days after the date of mailing by the Secretary of a notice of default with respect to the plan’s failure to meet one or more of the requirements of this subsection;
   (ii)
   any period set by a court of competent jurisdiction after a final determination that the plan fails to meet such requirements, or, if the court does not specify such period, any reasonable period determined by the Secretary on the basis of all the facts and circumstances, but in any event not less than 270 days after the determination has become final; or
   (iii)
   any additional period which the Secretary determines is reasonable or necessary for the correction of the default,
   whichever has the latest ending date.
   (5)
   Special rules for chaplains and self-employed ministers
   (A)
   Certain ministers may participate
   For purposes of this part—
   (i)
   In general
   A duly ordained, commissioned, or licensed minister of a church is described in paragraph (3)(B) if, in connection with the exercise of their ministry, the minister—
   (I)
   is a self-employed individual (within the meaning of section 401(c)(1)(B), or
   (II)
   is employed by an
   organization
   other than an
   organization
   which is described in section 501(c)(3) and with respect to which the minister shares common religious bonds.
   (ii)
   Treatment as employer and employee
   For purposes of sections 403(b)(1)(A) and 404(a)(10), a minister described in clause (i)(I) shall be treated as employed by the minister’s own employer which is an
   organization
   described in section 501(c)(3) and exempt from tax under section 501(a).
   (B)
   Special rules for applying
   section 403(b)
   to self-employed ministers
   In the case of a minister described in subparagraph (A)(i)(I)—
   (i)
   the minister’s includible
   compensation
   under
   section 403(b)(3)
   shall be determined by reference to the minister’s
   earned income
   (within the meaning of section 401(c)(2)) from such ministry rather than the amount of
   compensation
   which is received from an employer, and
   (ii)
   the years (and portions of years) in which such minister was a self-employed individual (within the meaning of
   section 401(c)(1)(B)
   ) with respect to such ministry shall be included for purposes of section 403(b)(4).
   (C)
   Effect on non-denominational plans
   If a duly ordained, commissioned, or licensed minister of a church in the exercise of his or her ministry participates in a
   church plan
   (within the meaning of this section) and in the exercise of such ministry is employed by an employer not otherwise participating in such
   church plan
   , then such employer may exclude such minister from being treated as an employee of such employer for purposes of applying sections 401(a)(3), 401(a)(4), and 401(a)(5), as in effect on
   September 1, 1974
   , and sections
   401(a)(4)
   ,
   401(a)(5)
   ,
   401(a)(26)
   ,
   401(k)(3)
   ,
   401(m)
   ,
   403(b)(1)(D)
   (including section 403(b)(12)), and 410 to any stock bonus, pension, profit-sharing, or annuity plan (including an annuity described in section 403(b) or a retirement income account described in section 403(b)(9)). The Secretary shall prescribe such regulations as may be necessary or appropriate to carry out the purpose of, and prevent the abuse of, this subparagraph.
   (D)
   Compensation taken into account only once
   If any
   compensation
   is taken into account in determining the amount of any contributions made to, or benefits to be provided under, any
   church plan,
   such
   compensation
   shall not also be taken into account in determining the amount of any contributions made to, or benefits to be provided under, any other stock bonus, pension, profit-sharing, or annuity plan which is not a
   church plan.
   (E)
   Exclusion
   In the case of a contribution to a
   church plan
   made on behalf of a minister described in subparagraph (A)(i)(II), such contribution shall not be included in the gross income of the minister to the extent that such contribution would not be so included if the minister was an employee of a church.
   (f)
   Multiemployer plan
   (1)
   Definition
   For purposes of this part, the term “
   multiemployer plan
   ” means a plan—
   (A)
   to which more than one employer is required to contribute,
   (B)
   which is maintained pursuant to one or more collective bargaining agreements between one or more employee
   organizations
   and more than one employer, and
   (C)
   which satisfies such other requirements as the Secretary of Labor may prescribe by regulation.
   (2)
   Cases of common control
   For purposes of this subsection, all trades or businesses (whether or not incorporated) which are under common control within the meaning of subsection (c) are considered a single employer.
   (3)
   Continuation of status after termination
   Notwithstanding paragraph (1), a plan is a
   multiemployer plan
   on and after its termination date under title IV of the
   Employee Retirement Income Security Act of 1974
   if the plan was a
   multiemployer plan
   under this subsection for the plan year preceding its termination date.
   (4)
   Transitional rule
   For any plan year which began before the date of the enactment of the
   Multiemployer Pension Plan Amendments Act of 1980
   , the term
   “multiemployer plan”
   means a plan described in this subsection as in effect immediately before that date.
   (5)
   Special election
   Within one year after the date of the enactment of the
   Multiemployer Pension Plan Amendments Act of 1980
   , a
   multiemployer plan
   may irrevocably elect, pursuant to procedures established by the
   Pension Benefit Guaranty Corporation
   and subject to the provisions of section 4403(b) and (c) of the
   Employee Retirement Income Security Act of 1974
   , that the plan shall not be treated as a
   multiemployer plan
   for any purpose under such Act or this title, if for each of the last 3 plan years ending prior to the effective date of the
   Multiemployer Pension Plan Amendments Act of 1980
   —
   (A)
   the plan was not a
   multiemployer plan
   because the plan was not a plan described in section 3(37)(A)(iii) of the
   Employee Retirement Income Security Act of 1974
   and section 414(f)(1)(C) (as such provisions were in effect on the day before the date of the enactment of the
   Multiemployer Pension Plan Amendments Act of 1980
   ); and
   (B)
   the plan had been identified as a plan that was not a
   multiemployer plan
   in substantially all its filings with the
   Pension Benefit Guaranty Corporation
   , the Secretary of Labor and the Secretary.
   (6)
   Election with regard to multiemployer status
   (A)
   Within 1 year after the enactment of the
   Pension Protection Act of 2006
   —
   (i)
   An election under paragraph (5) may be revoked, pursuant to procedures prescribed by the
   Pension Benefit Guaranty Corporation
   , if, for each of the 3 plan years prior to the date of the enactment of that Act, the plan would have been a
   multiemployer plan
   but for the election under paragraph (5), and
   (ii)
   a plan that meets the criteria in subparagraph (A) and (B) of paragraph (1) of this subsection or that is described in subparagraph (E) may, pursuant to procedures prescribed by the
   Pension Benefit Guaranty Corporation
   , elect to be a
   multiemployer plan,
   if—
   (I)
   for each of the 3 plan years immediately preceding the first plan year for which the election under this paragraph is effective with respect to the plan, the plan has met those criteria or is so described,
   (II)
   substantially all of the plan’s employer contributions for each of those plan years were made or required to be made by
   organizations
   that were exempt from tax under section 501, and
   (III)
   the plan was established prior to
   September 2, 1974
   .
   (B)
   An election under this paragraph shall be effective for all purposes under this Act
   [1]
   and under the
   Employee Retirement Income Security Act of 1974
   , starting with any plan year beginning on or after
   January 1, 1999
   , and ending before
   January 1, 2008
   , as designated by the plan in the election made under subparagraph (A)(ii).
   (C)
   Once made, an election under this paragraph shall be irrevocable, except that a plan described in subparagraph (A)(ii) shall cease to be a
   multiemployer plan
   as of the plan year beginning immediately after the first plan year for which the majority of its employer contributions were made or required to be made by
   organizations
   that were not exempt from tax under section 501.
   (D)
   The fact that a plan makes an election under subparagraph (A)(ii) does not imply that the plan was not a
   multiemployer plan
   prior to the date of the election or would not be a
   multiemployer plan
   without regard to the election.
   (E)
   A plan is described in this subparagraph if it is a plan sponsored by an
   organization
   which is described in section 501(c)(5) and exempt from tax under section 501(a) and which was established in Chicago, Illinois, on
   August 12, 1881
   .
   (F)
   Maintenance under collective bargaining agreement.—
   For purposes of this title and the
   Employee Retirement Income Security Act of 1974
   , a plan making an election under this paragraph shall be treated as maintained pursuant to a collective bargaining agreement if a collective bargaining agreement, expressly or otherwise, provides for or permits employer contributions to the plan by one or more employers that are signatory to such agreement, or participation in the plan by one or more employees of an employer that is signatory to such agreement, regardless of whether the plan was created, established, or maintained for such employees by virtue of another document that is not a collective bargaining agreement.
   (g)
   Plan administrator
   For purposes of this part, the term “
   plan administrator
   ” means—
   (1)
   the person specifically so designated by the terms of the instrument under which the plan is operated;
   (2)
   in the absence of a designation referred to in paragraph (1)—
   (A)
   in the case of a plan maintained by a single employer, such employer,
   (B)
   in the case of a plan maintained by two or more employers or jointly by one or more employers and one or more employee
   organizations
   , the association, committee, joint board of trustees, or other similar group of representatives of the parties who maintained the plan, or
   (C)
   in any case to which subparagraph (A) or (B) does not apply, such other person as the Secretary may by regulation, prescribe.
   (h)
   Tax treatment of certain contributions
   (1)
   In general
   Effective with respect to taxable years beginning after
   December 31, 1973
   , for purposes of this title, any amount contributed—
   (A)
   to an employees’ trust described in section 401(a), or
   (B)
   under a plan described in section 403(a), shall not be treated as having been made by the employer if it is designated as an employee contribution.
   (2)
   Designation by units of government
   For purposes of paragraph (1), in the case of any plan established by the government of any State or political subdivision thereof, or by any agency or instrumentality of any of the foregoing, or a
   governmental plan
   described in the last sentence of section 414(d) (relating to plans of Indian
   tribal
   governments), where the contributions of employing units are designated as employee contributions but where any employing unit picks up the contributions, the contributions so picked up shall be treated as employer contributions.
   (i)
   Defined contribution plan
   For purposes of this part, the term “
   defined contribution plan
   ” means a plan which provides for an individual account for each participant and for benefits based solely on the amount contributed to the participant’s account, and any income, expenses, gains and losses, and any forfeitures of accounts of other participants which may be allocated to such participant’s account.
   (j)
   Defined benefit plan
   For purposes of this part, the term “
   defined benefit plan
   ” means any plan which is not a
   defined contribution plan
   .
   (k)
   Certain plans
   A
   defined benefit plan
   which provides a benefit derived from employer contributions which is based partly on the balance of the separate account of a participant shall—
   (1)
   for purposes of section 410 (relating to minimum participation standards), be treated as a
   defined contribution plan
   ,
   (2)
   for purposes of sections 72(d) (relating to treatment of employee contributions as separate contract), 411(a)(7)(A) (relating to minimum vesting standards), 415 (relating to limitations on benefits and contributions under qualified plans), and 401(m) (relating to nondiscrimination tests for matching requirements and employee contributions), be treated as consisting of a
   defined contribution plan
   to the extent benefits are based on the separate account of a participant and as a
   defined benefit plan
   with respect to the remaining portion of benefits under the plan, and
   (3)
   for purposes of section 4975 (relating to tax on prohibited transactions), be treated as a
   defined benefit plan
   .
   (l)
   Merger and consolidations of plans or transfers of plan assets
   (1)
   In general
   A trust which forms a part of a plan shall not constitute a qualified trust under section 401 and a plan shall be treated as not described in section 403(a) unless in the case of any merger or consolidation of the plan with, or in the case of any transfer of assets or liabilities of such plan to, any other trust plan after
   September 2, 1974
   , each participant in the plan would (if the plan then terminated) receive a benefit immediately after the merger, consolidation, or transfer which is equal to or greater than the benefit he would have been entitled to receive immediately before the merger, consolidation, or transfer (if the plan had then terminated). The preceding sentence does not apply to any
   multiemployer plan
   with respect to any transaction to the extent that participants either before or after the transaction are covered under a
   multiemployer plan
   to which Title IV of the
   Employee Retirement Income Security Act of 1974
   applies.
   (2)
   Allocation of assets in plan spin-offs, etc.
   (A)
   In general
   In the case of a plan spin-off of a
   defined benefit plan
   , a trust which forms part of—
   (i)
   the original plan, or
   (ii)
   any plan spun off from such plan,
   shall not constitute a qualified trust under this section unless the
   applicable percentage
   of
   excess assets
   are allocated to each of such plans.
   (B)
   Applicable percentage
   For purposes of subparagraph (A), the term “
   applicable percentage
   ” means, with respect to each of the plans described in clauses (i) and (ii) of subparagraph (A), the percentage determined by dividing—
   (i)
   the excess (if any) of—
   (I)
   the sum of the funding target and target normal cost determined under section 430, over
   (II)
   the amount of the assets required to be allocated to the plan after the spin-off (without regard to this paragraph), by
   (ii)
   the sum of the excess amounts determined separately under clause (i) for all such plans.
   (C)
   Excess assets
   For purposes of subparagraph (A), the term “
   excess assets
   ” means an amount equal to the excess (if any) of—
   (i)
   the fair market value of the assets of the original plan immediately before the spin-off, over
   (ii)
   the amount of assets required to be allocated after the spin-off to all plans (determined without regard to this paragraph).
   (D)
   Certain spun-off plans not taken into account
   (i)
   In general
   A plan involved in a spin-off which is described in clause (ii), (iii), or (iv) shall not be taken into account for purposes of this paragraph, except that the amount determined under subparagraph (C)(ii) shall be increased by the amount of assets allocated to such plan.
   (ii)
   Plans transferred out of controlled groups
   A plan is described in this clause if, after such spin-off, such plan is maintained by an employer who is not a member of the same
   controlled group
   as the employer maintaining the original plan.
   (iii)
   Plans transferred out of multiple employer plans
   A plan as described in this clause if, after the spin-off, any employer maintaining such plan (and any member of the same
   controlled group
   as such employer) does not maintain any other plan remaining after the spin-off which is also maintained by another employer (or member of the same
   controlled group
   as such other employer) which maintained the plan in existence before the spin-off.
   (iv)
   Terminated plans
   A plan is described in this clause if, pursuant to the transaction involving the spin-off, the plan is terminated.
   (v)
   Controlled group
   For purposes of this subparagraph, the term “

-- [Content truncated - key provisions above]


-/
-- TODO: Add type definitions
-- TODO: Add main functions
-- TODO: Add theorems to prove