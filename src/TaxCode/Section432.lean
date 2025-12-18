/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 99ae4c79-84e9-47ae-a698-f4be11ce8168

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
# IRC Section 432 - Additional funding rules for multiemployer plans in endangered status or critical status

This file formalizes IRC §432 (Additional funding rules for multiemployer plans in endangered status or critical status).

## References
- [26 USC §432](https://www.law.cornell.edu/uscode/text/26/432)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 432 - Additional funding rules for multiemployer plans in endangered status or critical status
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   For purposes of this part, in the case of a multiemployer plan in effect on
   July 16, 2006
   —
   (1)
   if the plan is in endangered status—
   (A)
   the
   plan sponsor
   shall adopt and implement a funding improvement plan in accordance with the requirements of subsection (c), and
   (B)
   the requirements of subsection (d) shall apply during the
   funding plan adoption period
   and the funding improvement period,
   (2)
   if the plan is in critical status—
   (A)
   the
   plan sponsor
   shall adopt and implement a rehabilitation plan in accordance with the requirements of subsection (e), and
   (B)
   the requirements of subsection (f) shall apply during the
   rehabilitation plan adoption period
   and the rehabilitation period,
   (3)
   if the plan is in critical and declining status—
   (A)
   the requirements of paragraph (2) shall apply to the plan; and
   (B)
   the
   plan sponsor
   may, by plan amendment, suspend benefits in accordance with the requirements of subsection (e)(9), and
   (4)
   if the plan is an eligible multiemployer plan which is applying for or receiving special financial assistance under section 4262 of the
   Employee Retirement Income Security Act of 1974
   , the requirements of subsection (k) shall apply to the plan.
   (b)
   Determination of endangered and critical status
   For purposes of this section—
   (1)
   Endangered status
   A multiemployer plan is in endangered status for a plan year if, as determined by the plan actuary under paragraph (3), the plan is not in critical status for the plan year and is not described in paragraph (5), and, as of the beginning of the plan year, either—
   (A)
   the plan’s
   funded percentage
   for such plan year is less than 80 percent, or
   (B)
   the plan has an
   accumulated funding deficiency
   for such plan year, or is projected to have such an
   accumulated funding deficiency
   for any of the 6 succeeding plan years, taking into account any extension of amortization periods under section 431(d).
   For purposes of this section, a plan shall be treated as in seriously endangered status for a plan year if the plan is described in both subparagraphs (A) and (B).
   (2)
   Critical status
   A multiemployer plan is in critical status for a plan year if, as determined by the plan actuary under paragraph (3), the plan is described in 1 or more of the following subparagraphs as of the beginning of the plan year:
   (A)
   A plan is described in this subparagraph if—
   (i)
   the
   funded percentage
   of the plan is less than 65 percent, and
   (ii)
   the sum of—
   (I)
   the fair market value of plan assets, plus
   (II)
   the present value of the reasonably anticipated employer contributions for the current plan year and each of the 6 succeeding plan years, assuming that the terms of all collective bargaining agreements pursuant to which the plan is maintained for the current plan year continue in effect for succeeding plan years,
   is less than the present value of all nonforfeitable benefits projected to be payable under the plan during the current plan year and each of the 6 succeeding plan years (plus administrative expenses for such plan years).
   (B)
   A plan is described in this subparagraph if—
   (i)
   the plan has an
   accumulated funding deficiency
   for the current plan year, not taking into account any extension of amortization periods under section 431(d), or
   (ii)
   the plan is projected to have an
   accumulated funding deficiency
   for any of the 3 succeeding plan years (4 succeeding plan years if the
   funded percentage
   of the plan is 65 percent or less), not taking into account any extension of amortization periods under section 431(d).
   (C)
   A plan is described in this subparagraph if—
   (i)
   (I)
   the plan’s normal cost for the current plan year, plus interest (determined at the rate used for determining costs under the plan) for the current plan year on the amount of unfunded benefit liabilities under the plan as of the last date of the preceding plan year, exceeds
   (II)
   the present value of the reasonably anticipated employer and employee contributions for the current plan year,
   (ii)
   the present value, as of the beginning of the current plan year, of nonforfeitable benefits of
   inactive participants
   is greater than the present value of nonforfeitable benefits of
   active participants,
   and
   (iii)
   the plan has an
   accumulated funding deficiency
   for the current plan year, or is projected to have such a deficiency for any of the 4 succeeding plan years, not taking into account any extension of amortization periods under section 431(d).
   (D)
   A plan is described in this subparagraph if the sum of—
   (i)
   the fair market value of plan assets, plus
   (ii)
   the present value of the reasonably anticipated employer contributions for the current plan year and each of the 4 succeeding plan years, assuming that the terms of all collective bargaining agreements pursuant to which the plan is maintained for the current plan year continue in effect for succeeding plan years,
   is less than the present value of all benefits projected to be payable under the plan during the current plan year and each of the 4 succeeding plan years (plus administrative expenses for such plan years).
   (3)
   Annual certification by plan actuary
   (A)
   In general
   Not later than the 90th day of each plan year of a multiemployer plan, the plan actuary shall certify to the Secretary and to the
   plan sponsor
   —
   (i)
   whether or not the plan is in endangered status for such plan year, or would be in endangered status for such plan year but for paragraph (5), whether or not the plan is or will be in critical status for such plan year or for any of the succeeding 5 plan years, and whether or not the plan is or will be in critical and declining status for such plan year, and
   (ii)
   in the case of a plan which is in a funding improvement or rehabilitation period, whether or not the plan is making the scheduled progress in meeting the requirements of its funding improvement or rehabilitation plan.
   (B)
   Actuarial projections of assets and liabilities
   (i)
   In general
   Except as provided in clause (iv), in making the determinations and projections under this subsection, the plan actuary shall make projections required for the current and succeeding plan years of the current value of the assets of the plan and the present value of all liabilities to participants and beneficiaries under the plan for the current plan year as of the beginning of such year. The actuary’s projections shall be based on reasonable actuarial estimates, assumptions, and methods that, except as provided in clause (iii), offer the actuary’s best estimate of anticipated experience under the plan. The projected present value of liabilities as of the beginning of such year shall be determined based on the most recent of either—
   (I)
   the actuarial statement required under section 103(d) of the
   Employee Retirement Income Security Act of 1974
   with respect to the most recently filed annual report, or
   (II)
   the actuarial valuation for the preceding plan year.
   (ii)
   Determinations of future contributions
   Any actuarial projection of plan assets shall assume—
   (I)
   reasonably anticipated employer contributions for the current and succeeding plan years, assuming that the terms of the one or more collective bargaining agreements pursuant to which the plan is maintained for the current plan year continue in effect for succeeding plan years, or
   (II)
   that employer contributions for the most recent plan year will continue indefinitely, but only if the plan actuary determines there have been no significant demographic changes that would make such assumption unreasonable.
   (iii)
   Projected industry activity
   Any projection of activity in the industry or industries covered by the plan, including future covered employment and contribution levels, shall be based on information provided by the
   plan sponsor
   , which shall act reasonably and in good faith.
   (iv)
   Projections relating to critical status in succeeding plan years
   Clauses (i) and (ii) (other than the 2nd sentence of clause (i)) may be disregarded by a plan actuary in the case of any certification of whether a plan will be in critical status in a succeeding plan year, except that a
   plan sponsor
   may not elect to be in critical status for a plan year under paragraph (4) in any case in which the certification upon which such election would be based is made without regard to such clauses.
   (v)
   Projections of critical and declining status
   In determining whether a plan is in critical and declining status as described in subsection (e)(9), clauses (i), (ii), and (iii) shall apply, except that—
   (I)
   if reasonable, the plan actuary shall assume that each contributing employer in compliance continues to comply through the end of the rehabilitation period or such later time as provided in subsection (e)(3)(A)(ii) with the terms of the rehabilitation plan that correspond to the schedule adopted or imposed under subsection (e), and
   (II)
   the plan actuary shall take into account any suspensions of benefits described in subsection (e)(9) adopted in a prior plan year that are still in effect.
   (C)
   Penalty for failure to secure timely actuarial certification
   Any failure of the plan’s actuary to certify the plan’s status under this subsection by the date specified in subparagraph (A) shall be treated for purposes of section 502(c)(2) of the
   Employee Retirement Income Security Act of 1974
   as a failure or refusal by the plan administrator to file the annual report required to be filed with the Secretary under section 101(b)(1) of such Act.
   (D)
   Notice
   (i)
   In general
   In any case in which it is certified under subparagraph (A) that a multiemployer plan is or will be in endangered or critical status for a plan year or in which a
   plan sponsor
   elects to be in critical status for a plan year under paragraph (4), the
   plan sponsor
   shall, not later than 30 days after the date of the certification, provide notification of the endangered or critical status to the participants and beneficiaries, the bargaining parties, the
   Pension Benefit Guaranty Corporation
   , and the Secretary of Labor. In any case in which a
   plan sponsor
   elects to be in critical status for a plan year under paragraph (4), the
   plan sponsor
   shall notify the Secretary of such election not later than 30 days after the date of such certification or such other time as the Secretary may prescribe by regulations or other guidance.
   (ii)
   Plans in critical status
   If it is certified under subparagraph (A) that a multiemployer plan is or will be in critical status, the
   plan sponsor
   shall include in the notice under clause (i) an explanation of the possibility that—
   (I)
   adjustable benefits
   (as defined in subsection (e)(8)) may be reduced, and
   (II)
   such reductions may apply to participants and beneficiaries whose
   benefit commencement date
   is on or after the date such notice is provided for the first plan year in which the plan is in critical status.
   (iii)
   In the case of a multiemployer plan that would be in endangered status but for paragraph (5), the
   plan sponsor
   shall provide notice to the bargaining parties and the
   Pension Benefit Guaranty Corporation
   that the plan would be in endangered status but for such paragraph.
   (iv)
   Model notice
   The Secretary, in consultation with the Secretary of Labor, shall prescribe a model notice that a multiemployer plan may use to satisfy the requirements under clauses (ii) and (iii).
   (v)
   Notice of projection to be in critical status in a future plan year
   In any case in which it is certified under subparagraph (A)(i) that a multiemployer plan will be in critical status for any of 5 succeeding plan years (but not for the current plan year) and the
   plan sponsor
   of such plan has not made an election to be in critical status for the plan year under paragraph (4), the
   plan sponsor
   shall, not later than 30 days after the date of the certification, provide notification of the projected critical status to the
   Pension Benefit Guaranty Corporation
   .
   (4)
   Election to be in critical status
   Notwithstanding paragraph (2) and subject to paragraph (3)(B)(iv)—
   (A)
   the
   plan sponsor
   of a multiemployer plan that is not in critical status for a plan year but that is projected by the plan actuary, pursuant to the determination under paragraph (3), to be in critical status in any of the succeeding 5 plan years may, not later than 30 days after the date of the certification under paragraph (3)(A), elect to be in critical status effective for the current plan year,
   (B)
   the plan year in which the
   plan sponsor
   elects to be in critical status under subparagraph (A) shall be treated for purposes of this section as the first year in which the plan is in critical status, regardless of the date on which the plan first satisfies the criteria for critical status under paragraph (2), and
   (C)
   a plan that is in critical status under this paragraph shall not emerge from critical status except in accordance with subsection (e)(4)(B).
   (5)
   Special rule
   A plan is described in this paragraph if—
   (A)
   as part of the actuarial certification of endangered status under paragraph (3)(A) for the plan year, the plan actuary certifies that the plan is projected to no longer be described in either paragraph (1)(A) or paragraph (1)(B) as of the end of the tenth plan year ending after the plan year to which the certification relates, and
   (B)
   the plan was not in critical or endangered status for the immediately preceding plan year.
   (6)
   Critical and declining status
   For purposes of this section, a plan in critical status shall be treated as in critical and declining status if the plan is described in one or more of subparagraphs (A), (B), (C), and (D) of paragraph (2) and the plan is projected to become insolvent within the meaning of section 418E during the current plan year or any of the 14 succeeding plan years (19 succeeding plan years if the plan has a ratio of
   inactive participants
   to
   active participants
   that exceeds 2 to 1 or if the
   funded percentage
   of the plan is less than 80 percent).
   (7)
   Plans receiving special financial assistance
   If an eligible multiemployer plan receiving special financial assistance under section 4262 of the
   Employee Retirement Income Security Act of 1974
   meets the requirements of subsection (k)(2), notwithstanding the preceding paragraphs of this subsection, the plan shall be deemed to be in critical status for plan years beginning with the plan year in which the effective date for such assistance occurs and ending with the last plan year ending in 2051.
   (c)
   Funding improvement plan must be adopted for multiemployer plans in endangered status
   (1)
   In general
   In any case in which a multiemployer plan is in endangered status for a plan year, the
   plan sponsor
   , in accordance with this subsection—
   (A)
   shall adopt a funding improvement plan not later than 240 days following the required date for the actuarial certification of endangered status under subsection (b)(3)(A), and
   (B)
   within 30 days after the adoption of the funding improvement plan—
   (i)
   shall provide to the bargaining parties 1 or more schedules showing revised benefit structures, revised contribution structures, or both, which, if adopted, may reasonably be expected to enable the multiemployer plan to meet the
   applicable benchmarks
   in accordance with the funding improvement plan, including—
   (I)
   one proposal for reductions in the amount of future benefit accruals necessary to achieve the
   applicable benchmarks
   , assuming no amendments increasing contributions under the plan (other than amendments increasing contributions necessary to achieve the
   applicable benchmarks
   after amendments have reduced future benefit accruals to the maximum extent permitted by law), and
   (II)
   one proposal for increases in contributions under the plan necessary to achieve the
   applicable benchmarks
   , assuming no amendments reducing future benefit accruals under the plan, and
   (ii)
   may, if the
   plan sponsor
   deems appropriate, prepare and provide the bargaining parties with additional information relating to contribution rates or benefit reductions, alternative schedules, or other information relevant to achieving the
   applicable benchmarks
   in accordance with the funding improvement plan.
   For purposes of this section, the term “
   applicable benchmarks
   ” means the requirements applicable to the multiemployer plan under paragraph (3) (as modified by paragraph (5)).
   (2)
   Exception for years after process begins
   Paragraph (1) shall not apply to a plan year if such year is in a
   funding plan adoption period
   or funding improvement period by reason of the plan being in endangered status for a preceding plan year. For purposes of this section, such preceding plan year shall be the initial determination year with respect to the funding improvement plan to which it relates.
   (3)
   Funding improvement plan
   For purposes of this section—
   (A)
   In general
   A funding improvement plan is a plan which consists of the actions, including options or a range of options to be proposed to the bargaining parties, formulated to provide, based on reasonably anticipated experience and reasonable actuarial assumptions, for the attainment by the plan during the funding improvement period of the following requirements:
   (i)
   Increase in plan’s funding percentage
   The plan’s
   funded percentage
   as of the close of the funding improvement period equals or exceeds a percentage equal to the sum of—
   (I)
   such percentage as of the beginning of the first plan year for which the plan is certified to be in endangered status pursuant to paragraph (b)(3), plus
   (II)
   33 percent of the difference between 100 percent and the percentage under subclause (I).
   (ii)
   Avoidance of accumulated funding deficiencies
   No
   accumulated funding deficiency
   for the last plan year during the funding improvement period (taking into account any extension of amortization periods under
   section 431(d)
   ).
   (B)
   Seriously endangered plans
   In the case of a plan in seriously endangered status, except as provided in paragraph (5), subparagraph (A)(i)(II) shall be applied by substituting “20 percent” for “33 percent”.
   (4)
   Funding improvement period
   For purposes of this section—
   (A)
   In general
   The funding improvement period for any funding improvement plan adopted pursuant to this subsection is the 10-year period beginning on the first day of the first plan year of the multiemployer plan beginning after the earlier of—
   (i)
   the second anniversary of the date of the adoption of the funding improvement plan, or
   (ii)
   the expiration of the collective bargaining agreements in effect on the due date for the actuarial certification of endangered status for the initial determination year under subsection (b)(3)(A) and covering, as of such due date, at least 75 percent of the
   active participants
   in such multiemployer plan.
   (B)
   Seriously endangered plans
   In the case of a plan in seriously endangered status, except as provided in paragraph (5), subparagraph (A) shall be applied by substituting “15-year period” for “10-year period”.
   (C)
   Coordination with changes in status
   (i)
   Plans no longer in endangered status
   If the plan’s actuary certifies under subsection (b)(3)(A) for a plan year in any
   funding plan adoption period
   or funding improvement period that the plan is no longer in endangered status and is not in critical status, the
   funding plan adoption period
   or funding improvement period, whichever is applicable, shall end as of the close of the preceding plan year.
   (ii)
   Plans in critical status
   If the plan’s actuary certifies under subsection (b)(3)(A) for a plan year in any
   funding plan adoption period
   or funding improvement period that the plan is in critical status, the
   funding plan adoption period
   or funding improvement period, whichever is applicable, shall end as of the close of the plan year preceding the first plan year in the rehabilitation period with respect to such status.
   (D)
   Plans in endangered status at end of period
   If the plan’s actuary certifies under subsection (b)(3)(A) for the first plan year following the close of the period described in subparagraph (A) that the plan is in endangered status, the provisions of this subsection and subsection (d) shall be applied as if such first plan year were an initial determination year, except that the plan may not be amended in a manner inconsistent with the funding improvement plan in effect for the preceding plan year until a new funding improvement plan is adopted.
   (5)
   Special rules for seriously endangered plans more than 70 percent funded
   (A)
   In general
   If the
   funded percentage
   of a plan in seriously endangered status was more than 70 percent as of the beginning of the initial determination year—
   (i)
   paragraphs (3)(B) and (4)(B) shall apply only if the plan’s actuary certifies, within 30 days after the certification under subsection (b)(3)(A) for the initial determination year, that, based on the terms of the plan and the collective bargaining agreements in effect at the time of such certification, the plan is not projected to meet the requirements of paragraph (3)(A) (without regard to paragraphs (3)(B) and (4)(B)), and
   (ii)
   if there is a certification under clause (i), the plan may, in formulating its funding improvement plan, only take into account the rules of paragraph (3)(B) and (4)(B) for plan years in the funding improvement period beginning on or before the date on which the last of the collective bargaining agreements described in paragraph (4)(A)(ii) expires.
   (B)
   Special rule after expiration of agreements
   Notwithstanding subparagraph (A)(ii), if, for any plan year ending after the date described in subparagraph (A)(ii), the plan actuary certifies (at the time of the annual certification under subsection (b)(3)(A) for such plan year) that, based on the terms of the plan and collective bargaining agreements in effect at the time of that annual certification, the plan is not projected to be able to meet the requirements of paragraph (3)(A) (without regard to paragraphs (3)(B) and (4)(B)), paragraphs (3)(B) and (4)(B) shall continue to apply for such year.
   (6)
   Updates to funding improvement plans and schedules
   (A)
   Funding improvement plan
   The
   plan sponsor
   shall annually update the funding improvement plan and shall file the update with the plan’s annual report under section 104 of the
   Employee Retirement Income Security Act of 1974
   .
   (B)
   Schedules
   The
   plan sponsor
   shall annually update any schedule of contribution rates provided under this subsection to reflect the experience of the plan.
   (C)
   Duration of schedule
   A schedule of contribution rates provided by the
   plan sponsor
   and relied upon by bargaining parties in negotiating a collective bargaining agreement shall remain in effect for the duration of that collective bargaining agreement.
   (7)
   Imposition of schedule where failure to adopt funding improvement plan
   (A)
   Initial contribution schedule
   If—
   (i)
   a collective bargaining agreement providing for contributions under a multiemployer plan that was in effect at the time the plan entered endangered status expires, and
   (ii)
   after receiving one or more schedules from the
   plan sponsor
   under paragraph (1)(B), the bargaining parties with respect to such agreement fail to adopt a contribution schedule with terms consistent with the funding improvement plan and a schedule from the
   plan sponsor
   ,
   the
   plan sponsor
   shall implement the schedule described in paragraph (1)(B)(i)(I) beginning on the date specified in subparagraph (C).
   (B)
   Subsequent contribution schedule
   If—
   (i)
   a collective bargaining agreement providing for contributions under a multiemployer plan in accordance with a schedule provided by the
   plan sponsor
   pursuant to a funding improvement plan (or imposed under subparagraph (A)) expires while the plan is still in endangered status, and
   (ii)
   after receiving one or more updated schedules from the
   plan sponsor
   under paragraph (6)(B), the bargaining parties with respect to such agreement fail to adopt a contribution schedule with terms consistent with the updated funding improvement plan and a schedule from the
   plan sponsor
   ,
   then the contribution schedule applicable under the expired collective bargaining agreement, as updated and in effect on the date the collective bargaining agreement expires, shall be implemented by the
   plan sponsor
   beginning on the date specified in subparagraph (C).
   (C)
   Date of implementation
   The date specified in this subparagraph is the date which is 180 days after the date on which the collective bargaining agreement described in subparagraph (A) or (B) expires.
   (8)
   Funding plan adoption period
   For purposes of this section, the term “
   funding plan adoption period
   ” means the period beginning on the date of the certification under subsection (b)(3)(A) for the initial determination year and ending on the day before the first day of the funding improvement period.
   (d)
   Rules for operation of plan during adoption and improvement periods
   (1)
   Compliance with funding improvement plan
   (A)
   In general
   A plan may not be amended after the date of the adoption of a funding improvement plan under subsection (c) so as to be inconsistent with the funding improvement plan.
   (B)
   Special rules for benefit increases
   A plan may not be amended after the date of the adoption of a funding improvement plan under subsection (c) so as to increase benefits, including future benefit accruals, unless the plan actuary certifies that such increase is paid for out of additional contributions not contemplated by the funding improvement plan, and, after taking into account the benefit increase, the multiemployer plan still is reasonably expected to meet the applicable benchmark on the schedule contemplated in the funding improvement plan.
   (2)
   Special rules for plan adoption period
   During the period beginning on the date of the certification under subsection (b)(3)(A) for the initial determination year and ending on the date of the adoption of a funding improvement plan—
   (A)
   the
   plan sponsor
   may not accept a collective bargaining agreement or participation agreement with respect to the multiemployer plan that provides for—
   (i)
   a reduction in the level of contributions for any participants,
   (ii)
   a suspension of contributions with respect to any period of service, or
   (iii)
   any new direct or indirect exclusion of younger or newly hired employees from plan participation, and
   (B)
   no amendment of the plan which increases the liabilities of the plan by reason of any increase in benefits, any change in the accrual of benefits, or any change in the rate at which benefits become nonforfeitable under the plan may be adopted unless the amendment is required as a condition of qualification under part I of subchapter D of chapter 1 or to comply with other applicable law.
   (e)
   Rehabilitation plan must be adopted for multiemployer plans in critical status
   (1)
   In general
   In any case in which a multiemployer plan is in critical status for a plan year, the
   plan sponsor
   , in accordance with this subsection—
   (A)
   shall adopt a rehabilitation plan not later than 240 days following the required date for the actuarial certification of critical status under subsection (b)(3)(A), and
   (B)
   within 30 days after the adoption of the rehabilitation plan—
   (i)
   shall provide to the bargaining parties 1 or more schedules showing revised benefit structures, revised contribution structures, or both, which, if adopted, may reasonably be expected to enable the multiemployer plan to emerge from critical status in accordance with the rehabilitation plan, and
   (ii)
   may, if the
   plan sponsor
   deems appropriate, prepare and provide the bargaining parties with additional information relating to contribution rates or benefit reductions, alternative schedules, or other information relevant to emerging from critical status in accordance with the rehabilitation plan.
   The schedule or schedules described in subparagraph (B)(i) shall reflect reductions in future benefit accruals and
   adjustable benefits
   , and increases in contributions, that the
   plan sponsor
   determines are reasonably necessary to emerge from critical status. One schedule shall be designated as the default schedule and such schedule shall assume that there are no increases in contributions under the plan other than the increases necessary to emerge from critical status after future benefit accruals and other benefits (other than benefits the reduction or elimination of which are not permitted under
   section 411(d)(6)
   ) have been reduced to the maximum extent permitted by law.
   (2)
   Exception for years after process begins
   Paragraph (1) shall not apply to a plan year if such year is in a
   rehabilitation plan adoption period
   or rehabilitation period by reason of the plan being in critical status for a preceding plan year. For purposes of this section, such preceding plan year shall be the initial critical year with respect to the rehabilitation plan to which it relates.
   (3)
   Rehabilitation plan
   For purposes of this section—
   (A)
   In general
   A rehabilitation plan is a plan which consists of—
   (i)
   actions, including options or a range of options to be proposed to the bargaining parties, formulated, based on reasonably anticipated experience and reasonable actuarial assumptions, to enable the plan to cease to be in critical status by the end of the rehabilitation period and may include reductions in plan expenditures (including plan mergers and consolidations), reductions in future benefit accruals or increases in contributions, if agreed to by the bargaining parties, or any combination of such actions, or
   (ii)
   if the
   plan sponsor
   determines that, based on reasonable actuarial assumptions and upon exhaustion of all reasonable measures, the plan can not reasonably be expected to emerge from critical status by the end of the rehabilitation period, reasonable measures to emerge from critical status at a later time or to forestall possible insolvency (within the meaning of section 4245 of the
   Employee Retirement Income Security Act of 1974
   ).
   A rehabilitation plan must provide annual standards for meeting the requirements of such rehabilitation plan. Such plan shall also include the schedules required to be provided under paragraph (1)(B)(i) and if clause (ii) applies, shall set forth the alternatives considered, explain why the plan is not reasonably expected to emerge from critical status by the end of the rehabilitation period, and specify when, if ever, the plan is expected to emerge from critical status in accordance with the rehabilitation plan.
   (B)
   Updates to rehabilitation plan and schedules
   (i)
   Rehabilitation plan
   The
   plan sponsor
   shall annually update the rehabilitation plan and shall file the update with the plan’s annual report under section 104 of the
   Employee Retirement Income Security Act of 1974
   .
   (ii)
   Schedules
   The
   plan sponsor
   shall annually update any schedule of contribution rates provided under this subsection to reflect the experience of the plan.
   (iii)
   Duration of schedule
   A schedule of contribution rates provided by the
   plan sponsor
   and relied upon by bargaining parties in negotiating a collective bargaining agreement shall remain in effect for the duration of that collective bargaining agreement.
   (C)
   Imposition of schedule where failure to adopt rehabilitation plan
   (i)
   Initial contribution schedule
   If—
   (I)
   a collective bargaining agreement providing for contributions under a multiemployer plan that was in effect at the time the plan entered critical status expires, and
   (II)
   after receiving one or more schedules from the
   plan sponsor
   under paragraph (1)(B), the bargaining parties with respect to such agreement fail to adopt a contribution schedule with terms consistent with the rehabilitation plan and a schedule from the
   plan sponsor
   under paragraph (1)(B)(i),
   the
   plan sponsor
   shall implement the schedule described in the last sentence of paragraph (1) beginning on the date specified in clause (iii).
   (ii)
   Subsequent contribution schedule
   If—
   (I)
   a collective bargaining agreement providing for contributions under a multiemployer plan in accordance with a schedule provided by the
   plan sponsor
   pursuant to a rehabilitation plan (or imposed under subparagraph (C)(i)) expires while the plan is still in critical status, and
   (II)
   after receiving one or more updated schedules from the
   plan sponsor
   under subparagraph (B)(ii), the bargaining parties with respect to such agreement fail to adopt a contribution schedule with terms consistent with the updated rehabilitation plan and a schedule from the
   plan sponsor
   ,
   then the contribution schedule applicable under the expired collective bargaining agreement, as updated and in effect on the date the collective bargaining agreement expires, shall be implemented by the
   plan sponsor
   beginning on the date specified in clause (iii).
   (iii)
   Date of implementation
   The date specified in this subparagraph is the date which is 180 days after the date on which the collective bargaining agreement described in clause (ii) or (iii) expires.
   (4)
   Rehabilitation period
   For purposes of this section—
   (A)
   In general
   The rehabilitation period for a plan in critical status is the 10-year period beginning on the first day of the first plan year of the multiemployer plan following the earlier of—
   (i)
   the second anniversary of the date of the adoption of the rehabilitation plan, or
   (ii)
   the expiration of the collective bargaining agreements in effect on the due date for the actuarial certification of critical status for the initial critical year under subsection (a)(1) and covering, as of such date at least 75 percent of the
   active participants
   in such multiemployer plan.
   If a plan emerges from critical status as provided under subparagraph (B) before the end of such 10-year period, the rehabilitation period shall end with the plan year preceding the plan year for which the determination under subparagraph (B) is made.
   (B)
   Emergence
   (i)
   In general
   A plan in critical status shall remain in such status until a plan year for which the plan actuary certifies, in accordance with subsection (b)(3)(A), that—
   (I)
   the plan is not described in one or more of the subparagraphs in subsection (b)(2) as of the beginning of the plan year,
   (II)
   the plan is not projected to have an
   accumulated funding deficiency
   for the plan year or any of the 9 succeeding plan years, without regard to the use of the shortfall method but taking into account any extension of amortization periods under section 431(d)(2) or section 412(e) (as in effect prior to the enactment of the
   Pension Protection Act of 2006
   ), and
   (III)
   the plan is not projected to become insolvent within the meaning of section 418E for any of the 30 succeeding plan years.
   (ii)
   Plans with certain amortization extensions
   (I)
   Special emergence rule
   Notwithstanding clause (i), a plan in critical status that has an automatic extension of amortization periods under
   section 431(d)(1)
   shall no longer be in critical status if the plan actuary certifies for a plan year, in accordance with subsection (b)(3)(A), that—
   (aa)
   the plan is not projected to have an
   accumulated funding deficiency
   for the plan year or any of the 9 succeeding plan years, without regard to the use of the shortfall method but taking into account any extension of amortization periods under section 431(d)(1), and
   (bb)
   the plan is not projected to become insolvent within the meaning of section 418E for any of the 30 succeeding plan years,
   regardless of whether the plan is described in one or more of the subparagraphs in subsection (b)(2) as of the beginning of the plan year.
   (II)
   Reentry into critical status
   A plan that emerges from critical status under subclause (I) shall not reenter critical status for any subsequent plan year unless—
   (aa)
   the plan is projected to have an
   accumulated funding deficiency
   for the plan year or any of the 9 succeeding plan years, without regard to the use of the shortfall method but taking into account any extension of amortization periods under section 431(d), or

-- [Content truncated - key provisions above]


-/
-- TODO: Add type definitions
-- TODO: Add main functions
-- TODO: Add theorems to prove