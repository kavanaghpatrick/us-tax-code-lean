/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c2e6eba0-51c7-42fc-a5f8-0e6f0ca331f8

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
# IRC Section 430 - Minimum funding standards for single-employer defined benefit pension plans

This file formalizes IRC §430 (Minimum funding standards for single-employer defined benefit pension plans).

## References
- [26 USC §430](https://www.law.cornell.edu/uscode/text/26/430)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 430 - Minimum funding standards for single-employer defined benefit pension plans
   U.S. Code
   Notes
   Authorities (CFR)
   prev |
   next
   (a)
   Minimum required contribution
   For purposes of this section and section 412(a)(2)(A), except as provided in subsection (f), the term “
   minimum required contribution
   ” means, with respect to any plan year of a defined benefit plan which is not a multiemployer plan—
   (1)
   in any case in which the value of plan assets of the plan (as reduced under subsection (f)(4)(B)) is less than the funding target of the plan for the plan year, the sum of—
   (A)
   the
   target normal cost
   of the plan for the plan year,
   (B)
   the shortfall amortization charge (if any) for the plan for the plan year determined under subsection (c), and
   (C)
   the waiver amortization charge (if any) for the plan for the plan year as determined under subsection (e);
   (2)
   in any case in which the value of plan assets of the plan (as reduced under subsection (f)(4)(B)) equals or exceeds the funding target of the plan for the plan year, the
   target normal cost
   of the plan for the plan year reduced (but not below zero) by such excess.
   (b)
   Target normal cost
   For purposes of this section:
   (1)
   In general
   Except as provided in subsection (i)(2) with respect to plans in at-risk status, the term “
   target normal cost
   ” means, for any plan year, the excess of—
   (A)
   the sum of—
   (i)
   the present value of all benefits which are expected to accrue or to be earned under the plan during the plan year, plus
   (ii)
   the amount of plan-related expenses expected to be paid from plan assets during the plan year, over
   (B)
   the amount of mandatory
   employee
   contributions expected to be made during the plan year.
   (2)
   Special rule for increase in compensation
   For purposes of this subsection, if any benefit attributable to services performed in a preceding plan year is increased by reason of any increase in
   compensation
   during the current plan year, the increase in such benefit shall be treated as having accrued during the current plan year.
   (c)
   Shortfall amortization charge
   (1)
   In general
   For purposes of this section, the shortfall amortization charge for a plan for any plan year is the aggregate total (not less than zero) of the shortfall amortization installments for such plan year with respect to any shortfall amortization base which has not been fully amortized under this subsection.
   (2)
   Shortfall amortization installment
   For purposes of paragraph (1)—
   (A)
   Determination
   The shortfall amortization installments are the amounts necessary to amortize the shortfall amortization base of the plan for any plan year in level annual installments over the 7-plan-year period beginning with such plan year.
   (B)
   Shortfall installment
   The shortfall amortization installment for any plan year in the 7-plan-year period under subparagraph (A) with respect to any shortfall amortization base is the annual installment determined under subparagraph (A) for that year for that base.
   (C)
   Segment rates
   In determining any shortfall amortization installment under this paragraph, the
   plan sponsor
   shall use the segment rates determined under subparagraph (C) of subsection (h)(2), applied under rules similar to the rules of subparagraph (B) of subsection (h)(2).
   (D)
   Special election for eligible plan years
   (i)
   In general
   If a
   plan sponsor
   elects to apply this subparagraph with respect to the shortfall amortization base of a plan for any
   eligible plan year
   (in this subparagraph and paragraph (7) referred to as an “election year”), then, notwithstanding subparagraphs (A) and (B)—
   (I)
   the shortfall amortization installments with respect to such base shall be determined under clause (ii) or (iii), whichever is specified in the election, and
   (II)
   the shortfall amortization installment for any plan year in the 9-plan-year period described in clause (ii) or the 15-plan-year period described in clause (iii), respectively, with respect to such shortfall amortization base is the annual installment determined under the applicable clause for that year for that base.
   (ii)
   2 plus 7 amortization schedule
   The shortfall amortization installments determined under this clause are—
   (I)
   in the case of the first 2 plan years in the 9-plan-year period beginning with the election year, interest on the shortfall amortization base of the plan for the election year (determined using the
   effective interest rate
   for the plan for the election year), and
   (II)
   in the case of the last 7 plan years in such 9-plan-year period, the amounts necessary to amortize the remaining balance of the shortfall amortization base of the plan for the election year in level annual installments over such last 7 plan years (using the segment rates under subparagraph (C) for the election year).
   (iii)
   15-year amortization
   The shortfall amortization installments determined under this subparagraph are the amounts necessary to amortize the shortfall amortization base of the plan for the election year in level annual installments over the 15-plan-year period beginning with the election year (using the segment rates under subparagraph (C) for the election year).
   (iv)
   Election
   (I)
   In general
   The
   plan sponsor
   of a plan may elect to have this subparagraph apply to not more than 2
   eligible plan years
   with respect to the plan, except that in the case of a plan described in section 106 of the
   Pension Protection Act of 2006
   , the
   plan sponsor
   may only elect to have this subparagraph apply to a plan year beginning in 2011.
   (II)
   Amortization schedule
   Such election shall specify whether the amortization schedule under clause (ii) or (iii) shall apply to an election year, except that if a
   plan sponsor
   elects to have this subparagraph apply to 2
   eligible plan years
   , the
   plan sponsor
   must elect the same schedule for both years.
   (III)
   Other rules
   Such election shall be made at such time, and in such form and manner, as shall be prescribed by the Secretary, and may be revoked only with the consent of the Secretary. The Secretary shall, before granting a revocation request, provide the
   Pension Benefit Guaranty Corporation
   an opportunity to comment on the conditions applicable to the treatment of any portion of the election year shortfall amortization base that remains unamortized as of the revocation date.
   (v)
   Eligible plan year
   For purposes of this subparagraph, the term “
   eligible plan year
   ” means any plan year beginning in 2008, 2009, 2010, or 2011, except that a plan year shall only be treated as an
   eligible plan year
   if the
   due date
   under subsection (j)(1) for the payment of the
   minimum required contribution
   for such plan year occurs on or after the date of the enactment of this subparagraph.
   (vi)
   Reporting
   A
   plan sponsor
   of a plan who makes an election under clause (i) shall—
   (I)
   give notice of the election to participants and beneficiaries of the plan, and
   (II)
   inform the
   Pension Benefit Guaranty Corporation
   of such election in such form and manner as the Director of the
   Pension Benefit Guaranty Corporation
   may prescribe.
   (vii)
   Increases in required installments in certain cases
   For increases in required contributions in cases of excess
   compensation
   or extraordinary dividends or stock redemptions, see paragraph (7).
   (3)
   Shortfall amortization base
   For purposes of this section, the shortfall amortization base of a plan for a plan year is—
   (A)
   the funding shortfall of such plan for such plan year, minus
   (B)
   the present value (determined using the segment rates determined under subparagraph (C) of subsection (h)(2), applied under rules similar to the rules of subparagraph (B) of subsection (h)(2)) of the aggregate total of the shortfall amortization installments and waiver amortization installments which have been determined for such plan year and any succeeding plan year with respect to the shortfall amortization bases and waiver amortization bases of the plan for any plan year preceding such plan year.
   (4)
   Funding shortfall
   For purposes of this section, the funding shortfall of a plan for any plan year is the excess (if any) of—
   (A)
   the funding target of the plan for the plan year, over
   (B)
   the value of plan assets of the plan (as reduced under subsection (f)(4)(B)) for the plan year which are held by the plan on the valuation date.
   (5)
   Exemption from new shortfall amortization base
   In any case in which the value of plan assets of the plan (as reduced under subsection (f)(4)(A)) is equal to or greater than the funding target of the plan for the plan year, the shortfall amortization base of the plan for such plan year shall be zero.
   (6)
   Early deemed amortization upon attainment of funding target
   In any case in which the funding shortfall of a plan for a plan year is zero, for purposes of determining the shortfall amortization charge for such plan year and succeeding plan years, the shortfall amortization bases for all preceding plan years (and all shortfall amortization installments determined with respect to such bases) shall be reduced to zero.
   (7)
   Increases in alternate required installments in cases of excess compensation or extraordinary dividends or stock redemptions
   (A)
   In general
   If there is an
   installment acceleration amount
   with respect to a plan for any plan year in the
   restriction period
   with respect to an election year under paragraph (2)(D), then the shortfall amortization installment otherwise determined and payable under such paragraph for such plan year shall, subject to the limitation under subparagraph (B), be increased by such amount.
   (B)
   Total installments limited to shortfall base
   Subject to rules prescribed by the Secretary, if a shortfall amortization installment with respect to any shortfall amortization base for an election year is required to be increased for any plan year under subparagraph (A)—
   (i)
   such increase shall not result in the amount of such installment exceeding the present value of such installment and all succeeding installments with respect to such base (determined without regard to such increase but after application of clause (ii)), and
   (ii)
   subsequent shortfall amortization installments with respect to such base shall, in reverse order of the otherwise
   required installments
   , be reduced to the extent necessary to limit the present value of such subsequent shortfall amortization installments (after application of this paragraph) to the present value of the remaining unamortized shortfall amortization base.
   (C)
   Installment acceleration amount
   For purposes of this paragraph—
   (i)
   In general
   The term “
   installment acceleration amount
   ” means, with respect to any plan year in a
   restriction period
   with respect to an election year, the sum of—
   (I)
   the aggregate amount of
   excess employee compensation
   determined under subparagraph (D) with respect to all
   employees
   for the plan year, plus
   (II)
   the aggregate amount of extraordinary dividends and redemptions determined under subparagraph (E) for the plan year.
   (ii)
   Annual limitation
   The
   installment acceleration amount
   for any plan year shall not exceed the excess (if any) of—
   (I)
   the sum of the shortfall amortization installments for the plan year and all preceding plan years in the amortization period elected under paragraph (2)(D) with respect to the shortfall amortization base with respect to an election year, determined without regard to paragraph (2)(D) and this paragraph, over
   (II)
   the sum of the shortfall amortization installments for such plan year and all such preceding plan years, determined after application of paragraph (2)(D) (and in the case of any preceding plan year, after application of this paragraph).
   (iii)
   Carryover of excess installment acceleration amounts
   (I)
   In general
   If the
   installment acceleration amount
   for any plan year (determined without regard to clause (ii)) exceeds the limitation under clause (ii), then, subject to subclause (II), such excess shall be treated as an
   installment acceleration amount
   with respect to the succeeding plan year.
   (II)
   Cap to apply
   If any amount treated as an
   installment acceleration amount
   under subclause (I) or this subclause with respect any succeeding plan year, when added to other
   installment acceleration amounts
   (determined without regard to clause (ii)) with respect to the plan year, exceeds the limitation under clause (ii), the portion of such amount representing such excess shall be treated as an
   installment acceleration amount
   with respect to the next succeeding plan year.
   (III)
   Limitation on years to which amounts carried for
   No amount shall be carried under subclause (I) or (II) to a plan year which begins after the first plan year following the last plan year in the
   restriction period
   (or after the second plan year following such last plan year in the case of an election year with respect to which 15-year amortization was elected under paragraph (2)(D)).
   (IV)
   Ordering rules
   For purposes of applying subclause (II),
   installment acceleration amounts
   for the plan year (determined without regard to any carryover under this clause) shall be applied first against the limitation under clause (ii) and then carryovers to such plan year shall be applied against such limitation on a first-in, first-out basis.
   (D)
   Excess employee compensation
   For purposes of this paragraph—
   (i)
   In general
   The term “
   excess employee compensation
   ” means, with respect to any
   employee
   for any plan year, the excess (if any) of—
   (I)
   the aggregate amount includible in income under this chapter for remuneration during the calendar year in which such plan year begins for services performed by the
   employee
   for the
   plan sponsor
   (whether or not performed during such calendar year), over
   (II)
   $1,000,000.
   (ii)
   Amounts set aside for nonqualified deferred compensation
   If during any calendar year assets are set aside or reserved (directly or indirectly) in a trust (or other arrangement as determined by the Secretary), or transferred to such a trust or other arrangement, by a
   plan sponsor
   for purposes of paying deferred
   compensation
   of an
   employee
   under a nonqualified deferred
   compensation
   plan (as defined in section 409A) of the
   plan sponsor
   , then, for purposes of clause (i), the amount of such assets shall be treated as remuneration of the
   employee
   includible in income for the calendar year unless such amount is otherwise includible in income for such year. An amount to which the preceding sentence applies shall not be taken into account under this paragraph for any subsequent calendar year.
   (iii)
   Only remuneration for certain post-2009 services counted
   Remuneration shall be taken into account under clause (i) only to the extent attributable to services performed by the
   employee
   for the
   plan sponsor
   after
   February 28, 2010
   .
   (iv)
   Exception for certain equity payments
   (I)
   In general
   There shall not be taken into account under clause (i)(I) any amount includible in income with respect to the granting after
   February 28, 2010
   , of service recipient stock (within the meaning of
   section 409A
   ) that, upon such grant, is subject to a substantial risk of forfeiture (as defined under section 83(c)(1)) for at least 5 years from the date of such grant.
   (II)
   Secretarial authority
   The Secretary may by regulation provide for the application of this clause in the case of a person other than a corporation.
   (v)
   Other exceptions
   The following amounts includible in income shall not be taken into account under clause (i)(I):
   (I)
   Commissions
   Any remuneration payable on a commission basis solely on account of income directly generated by the individual performance of the individual to whom such remuneration is payable.
   (II)
   Certain payments under existing contracts
   Any remuneration consisting of nonqualified deferred
   compensation
   , restricted stock, stock options, or stock appreciation rights payable or granted under a written binding contract that was in effect on
   March 1, 2010
   , and which was not modified in any material respect before such remuneration is paid.
   (vi)
   Self-employed individual treated as employee
   The term “
   employee
   ” includes, with respect to a calendar year, a self-employed individual who is treated as an
   employee
   under
   section 401(c)
   for the taxable year ending during such calendar year, and the term
   “compensation”
   shall include
   earned income
   of such individual with respect to such self-employment.
   (vii)
   Indexing of amount
   In the case of any calendar year beginning after 2010, the dollar amount under clause (i)(II) shall be increased by an amount equal to—
   (I)
   such dollar amount, multiplied by
   (II)
   the cost-of-living adjustment determined under section 1(f)(3) for the calendar year, determined by substituting “calendar year 2009” for “calendar year 2016” in subparagraph (A)(ii) thereof.
   If the amount of any increase under clause (i) is not a multiple of $1,000, such increase shall be rounded to the next lowest multiple of $1,000.
   (E)
   Extraordinary dividends and redemptions
   (i)
   In general
   The amount determined under this subparagraph for any plan year is the excess (if any) of the sum of the dividends declared during the plan year by the
   plan sponsor
   plus the aggregate amount paid for the redemption of stock of the
   plan sponsor
   redeemed during the plan year over the greater of—
   (I)
   the adjusted net income (within the meaning of section 4043 of the
   Employee Retirement Income Security Act of 1974
   ) of the
   plan sponsor
   for the preceding plan year, determined without regard to any reduction by reason of interest, taxes, depreciation, or amortization, or
   (II)
   in the case of a
   plan sponsor
   that determined and declared dividends in the same manner for at least 5 consecutive years immediately preceding such plan year, the aggregate amount of dividends determined and declared for such plan year using such manner.
   (ii)
   Only certain post-2009 dividends and redemptions counted
   For purposes of clause (i), there shall only be taken into account dividends declared, and redemptions occurring, after
   February 28, 2010
   .
   (iii)
   Exception for intra-group dividends
   Dividends paid by one member of a
   controlled group
   (as defined in
   section 412(d)(3)
   ) to another member of such group shall not be taken into account under clause (i).
   (iv)
   Exception for certain redemptions
   Redemptions that are made pursuant to a plan maintained with respect to
   employees
   , or that are made on account of the death, disability, or termination of employment of an
   employee
   or shareholder, shall not be taken into account under clause (i).
   (v)
   Exception for certain preferred stock
   (I)
   In general
   Dividends and redemptions with respect to
   applicable preferred stock
   shall not be taken into account under clause (i) to the extent that dividends accrue with respect to such stock at a specified rate in all events and without regard to the
   plan sponsor’
   s income, and interest accrues on any unpaid dividends with respect to such stock.
   (II)
   Applicable preferred stock
   For purposes of subclause (I), the term “
   applicable preferred stock
   ” means preferred stock which was issued before
   March 1, 2010
   (or which was issued after such date and is held by an
   employee
   benefit plan subject to the provisions of title I of the
   Employee Retirement Income Security Act of 1974
   ).
   (F)
   Other definitions and rules
   For purposes of this paragraph—
   (i)
   Plan sponsor
   The term “
   plan sponsor
   ” includes any member of the
   plan sponsor
   ’s
   controlled group
   (as defined in
   section 412(d)(3)
   ).
   (ii)
   Restriction period
   The term “
   restriction period
   ” means, with respect to any election year—
   (I)
   except as provided in subclause (II), the 3-year period beginning with the election year (or, if later, the first plan year beginning after
   December 31, 2009
   ), and
   (II)
   if the
   plan sponsor
   elects 15-year amortization for the shortfall amortization base for the election year, the 5-year period beginning with the election year (or, if later, the first plan year beginning after
   December 31, 2009
   ).
   (iii)
   Elections for multiple plans
   If a
   plan sponsor
   makes elections under paragraph (2)(D) with respect to 2 or more plans, the Secretary shall provide rules for the application of this paragraph to such plans, including rules for the ratable allocation of any
   installment acceleration amount
   among such plans on the basis of each plan’s relative reduction in the plan’s shortfall amortization installment for the first plan year in the amortization period described in subparagraph (A) (determined without regard to this paragraph).
   (iv)
   Mergers and acquisitions
   The Secretary shall prescribe rules for the application of paragraph (2)(D) and this paragraph in any case where there is a merger or acquisition involving a
   plan sponsor
   making the election under paragraph (2)(D).
   (8)
   15-year amortization
   With respect to plan years beginning after
   December 31, 2021
   (or, at the election of the
   plan sponsor,
   plan years beginning after
   December 31, 2018
   ,
   December 31, 2019
   , or
   December 31, 2020
   )—
   (A)
   the shortfall amortization bases for all plan years preceding the first plan year beginning after
   December 31, 2021
   (or after whichever earlier date is elected pursuant to this paragraph), and all shortfall amortization installments determined with respect to such bases, shall be reduced to zero, and
   (B)
   subparagraphs (A) and (B) of paragraph (2) shall each be applied by substituting “15-plan-year period” for “7-plan-year period”.
   (d)
   Rules relating to funding target
   For purposes of this section—
   (1)
   Funding target
   Except as provided in subsection (i)(1) with respect to plans in at-risk status, the funding target of a plan for a plan year is the present value of all benefits accrued or earned under the plan as of the beginning of the plan year.
   (2)
   Funding target attainment percentage
   The “funding target attainment percentage” of a plan for a plan year is the ratio (expressed as a percentage) which—
   (A)
   the value of plan assets for the plan year (as reduced under subsection (f)(4)(B)), bears to
   (B)
   the funding target of the plan for the plan year (determined without regard to subsection (i)(1)).
   (e)
   Waiver amortization charge
   (1)
   Determination of waiver amortization charge
   The waiver amortization charge (if any) for a plan for any plan year is the aggregate total of the waiver amortization installments for such plan year with respect to the waiver amortization bases for each of the 5 preceding plan years.
   (2)
   Waiver amortization installment
   For purposes of paragraph (1)—
   (A)
   Determination
   The waiver amortization installments are the amounts necessary to amortize the waiver amortization base of the plan for any plan year in level annual installments over a period of 5 plan years beginning with the succeeding plan year.
   (B)
   Waiver installment
   The waiver amortization installment for any plan year in the 5-year period under subparagraph (A) with respect to any waiver amortization base is the annual installment determined under subparagraph (A) for that year for that base.
   (3)
   Interest rate
   In determining any waiver amortization installment under this subsection, the
   plan sponsor
   shall use the segment rates determined under subparagraph (C) of subsection (h)(2), applied under rules similar to the rules of subparagraph (B) of subsection (h)(2).
   (4)
   Waiver amortization base
   The waiver amortization base of a plan for a plan year is the amount of the waived funding deficiency (if any) for such plan year under section 412(c).
   (5)
   Early deemed amortization upon attainment of funding target
   In any case in which the funding shortfall of a plan for a plan year is zero, for purposes of determining the waiver amortization charge for such plan year and succeeding plan years, the waiver amortization bases for all preceding plan years (and all waiver amortization installments determined with respect to such bases) shall be reduced to zero.
   (f)
   Reduction of minimum required contribution by prefunding balance and funding standard carryover balance
   (1)
   Election to maintain balances
   (A)
   Prefunding balance
   The
   plan sponsor
   of a defined benefit plan which is not a multiemployer plan may elect to maintain a prefunding balance.
   (B)
   Funding standard carryover balance
   (i)
   In general
   In the case of a defined benefit plan (other than a multiemployer plan) described in clause (ii), the
   plan sponsor
   may elect to maintain a funding standard carryover balance, until such balance is reduced to zero.
   (ii)
   Plans maintaining funding standard account in 2007
   A plan is described in this clause if the plan—
   (I)
   was in effect for a plan year beginning in 2007, and
   (II)
   had a positive balance in the funding standard account under section 412(b) as in effect for such plan year and determined as of the end of such plan year.
   (2)
   Application of balances
   A prefunding balance and a funding standard carryover balance maintained pursuant to this paragraph—
   (A)
   shall be available for crediting against the
   minimum required contribution
   , pursuant to an election under paragraph (3),
   (B)
   shall be applied as a reduction in the amount treated as the value of plan assets for purposes of this section, to the extent provided in paragraph (4), and
   (C)
   may be reduced at any time, pursuant to an election under paragraph (5).
   (3)
   Election to apply balances against minimum required contribution
   (A)
   In general
   Except as provided in subparagraphs (B) and (C), in the case of any plan year in which the
   plan sponsor
   elects to credit against the
   minimum required contribution
   for the current plan year all or a portion of the prefunding balance or the funding standard carryover balance for the current plan year (not in excess of such
   minimum required contribution
   ), the
   minimum required contribution
   for the plan year shall be reduced as of the first day of the plan year by the amount so credited by the
   plan sponsor.
   For purposes of the preceding sentence, the
   minimum required contribution
   shall be determined after taking into account any waiver under section 412(c).
   (B)
   Coordination with funding standard carryover balance
   To the extent that any plan has a funding standard carryover balance greater than zero, no amount of the prefunding balance of such plan may be credited under this paragraph in reducing the
   minimum required contribution
   .
   (C)
   Limitation for underfunded plans
   The preceding provisions of this paragraph shall not apply for any plan year if the ratio (expressed as a percentage) which—
   (i)
   the value of plan assets for the preceding plan year (as reduced under paragraph (4)(C)), bears to
   (ii)
   the funding target of the plan for the preceding plan year (determined without regard to subsection (i)(1)),
   is less than 80 percent. In the case of plan years beginning in 2008, the ratio under this subparagraph may be determined using such methods of estimation as the Secretary may prescribe.
   (D)
   Special rule for certain years of plans maintained by charities
   (i)
   In general
   For purposes of applying subparagraph (C) for plan years beginning after
   August 31, 2009
   , and before
   September 1, 2011
   , the ratio determined under such subparagraph for the preceding plan year of a plan shall be the greater of—
   (I)
   such ratio, as determined without regard to this subsection, or
   (II)
   the ratio for such plan for the plan year beginning after
   August 31, 2007
   and before
   September 1, 2008
   , as determined under rules prescribed by the Secretary.
   (ii)
   Special rule
   In the case of a plan for which the valuation date is not the first day of the plan year—
   (I)
   clause (i) shall apply to plan years beginning after
   December 31, 2007
   , and before
   January 1, 2010
   , and
   (II)
   clause (i)(II) shall apply based on the last plan year beginning before
   September 1, 2007
   , as determined under rules prescribed by the Secretary.
   (iii)
   Limitation to charities
   This subparagraph shall not apply to any plan unless such plan is maintained exclusively by one or more organizations described in section 501(c)(3).
   (4)
   Effect of balances on amounts treated as value of plan assets
   In the case of any plan maintaining a prefunding balance or a funding standard carryover balance pursuant to this subsection, the amount treated as the value of plan assets shall be deemed to be such amount, reduced as provided in the following subparagraphs:

-- [Content truncated - key provisions above]

-- TODO: Add type definitions
-- TODO: Add main functions
-- TODO: Add theorems to prove