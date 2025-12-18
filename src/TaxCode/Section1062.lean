/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dd02ed4b-1619-4956-8f21-80e027adeca8
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token ';'; expected command
unexpected identifier; expected 'instance'-/
set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

def Currency := Int

structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913
  deriving DecidableEq, Repr

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
# IRC Section 1062 - Gain from the sale or exchange of qualified farmland property to qualified farmers

This file formalizes IRC §1062 (Gain from the sale or exchange of qualified farmland property to qualified farmers).

## References
- [26 USC §1062](https://www.law.cornell.edu/uscode/text/26/1062)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1062 - Gain from the sale or exchange of qualified farmland property to qualified farmers
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Election to pay tax in installments
   In the case of gain from the sale or exchange of
   qualified farmland property
   to a
   qualified farmer,
   at the election of the taxpayer, the portion of the
   net income tax
   of such taxpayer for the taxable year of the sale or exchange which is equal to the applicable net tax liability shall be paid in 4 equal installments.
   (b)
   Rules relating to installment payments
   (1)
   Date for payment of installments
   If an election is made under subsection (a), the first installment shall be paid on the due date (determined without regard to any extension of time for filing the return) for the return of tax for the taxable year in which the sale or exchange occurs and each succeeding installment shall be paid on the due date (as so determined) for the return of tax for the taxable year following the taxable year with respect to which the preceding installment was made.
   (2)
   Acceleration of payment
   (A)
   In general
   If there is an addition to tax for failure to timely pay any installment required under this section, then the unpaid portion of all remaining installments shall be due on the date of such failure.
   (B)
   Individuals
   In the case of an individual, if the individual dies, then the unpaid portion of all remaining installment shall be paid on the due date for the return of tax for the taxable year in which the taxpayer dies.
   (C)
   C corporations
   In the case of a taxpayer which is a C corporation, trust, or estate, if there is a liquidation or sale of substantially all the assets of the taxpayer (including in a title 11 or similar case), a cessation of business by the taxpayer (in the case of a C corporation), or any similar circumstance, then the unpaid portion of all remaining installments shall be due on the date of such event (or in the case of a title 11 or similar case, the day before the petition is filed). The preceding sentence shall not apply to the sale of substantially all the assets of a taxpayer to a buyer if such buyer enters into an agreement with the Secretary under which such buyer is liable for the remaining installments due under this subsection in the same manner as if such buyer were the taxpayer.
   (3)
   Proration of deficiency to installments
   If an election is made under subsection (a) to pay the applicable net tax liability in installments and a deficiency has been assessed with respect to such applicable net tax liability, the deficiency shall be prorated to the installments payable under subsection (a). The part of the deficiency so prorated to any installment the date for payment of which has not arrived shall be collected at the same time as, and as a part of, such installment. The part of the deficiency so prorated to any installment the date for payment of which has arrived shall be paid upon notice and demand from the Secretary. This section shall not apply if the deficiency is due to negligence, to intentional disregard of rules and regulations, or to fraud with intent to evade tax.
   (c)
   Election
   (1)
   In general
   Any election under subsection (a) shall be made not later than the due date for the return of tax for the taxable year described in subsection (a).
   (2)
   Partnerships and S corporations
   In the case of a sale or exchange described in subsection (a) by a partnership or S corporation, the election under subsection (a) shall be made at the partner or shareholder level. The Secretary may prescribe such regulations or other guidance as necessary to carry out the purposes of this paragraph.
   (d)
   Definitions
   For purposes of this section—
   (1)
   Applicable net tax liability
   (A)
   In general
   The applicable net tax liability with respect to the sale or exchange of any property described in subsection (a) is the excess (if any) of—
   (i)
   such taxpayer’s
   net income tax
   for the taxable year, over
   (ii)
   such taxpayer’s
   net income tax
   for such taxable year determined without regard to any gain recognized from the sale or exchange of such property.
   (B)
   Net income tax
   The term “
   net income tax
   ” means the regular tax liability reduced by the credits allowed under subparts A, B, and D of part IV of subchapter A.
   (2)
   Qualified farmland property
   (A)
   In general
   The term “
   qualified farmland property
   ” means real property located in the United States—
   (i)
   which—
   (I)
   has been used by the taxpayer as a
   farm
   for
   farming purposes
   , or
   (II)
   leased by the taxpayer to a
   qualified farmer
   for
   farming purposes
   ,
   during substantially all of the 10-year period ending on the date of the qualified sale or exchange, and
   (ii)
   which is subject to a covenant or other legally enforceable restriction which prohibits the use of such property other than as a
   farm
   for
   farming purposes
   for any period before the date that is 10 years after the date of the sale or exchange described in subsection (a).
   For purposes of clause (i), property which is used or leased by a partnership or S corporation in a manner described in such clause shall be treated as used or leased in such manner by each person who holds a direct or indirect interest in such partnership or S corporation.
   (B)
   Farm; farming purposes
   The terms “
   farm
   ” and “
   farming purposes
   ” have the respective meanings given such terms under section 2032A(e).
   (3)
   Qualified farmer
   The term “
   qualified farmer
   ” means any individual who is actively engaged in farming (within the meaning of subsections (b) and (c) of section 1001 of the Food Security Act of 1986
   [1]
   (
   7 U.S.C. 1308–1(b)
   and (c))).
   (e)
   Return requirement
   A taxpayer making an election under subsection (a) shall include with the return for the taxable year of the sale or exchange described in subsection (a) a copy of the covenant or other legally enforceable restriction described in subsection (d)(2)(A)(ii).
   (Added
   Pub. L. 119–21, title VII, § 70437(a)
   ,
   July 4, 2025
   ,
   139 Stat. 248
   .)
   [1]
   See References in Text note below.
   Editorial Notes
   References in Text
   Subsections (b) and (c) of section 1001 of the Food Security Act of 1986, referred to in subsec. (d)(3), probably should be a reference to subsections (b) and (c) of section 1001A of the
   Food Security Act of 1985
   , which is classified to section 1308–1(b), (c) of Title 7, Agriculture.
   Prior Provisions
   A prior
   section 1062
   was renumbered
   section 1063 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date
   Pub. L. 119–21, title VII, § 70437(c)
   ,
   July 4, 2025
   ,
   139 Stat. 250
   , provided that:
   “The amendments made by this section [enacting this section and renumbering former
   section 1062 of this title
   as section 1063] shall apply to sales or exchanges in taxable years beginning after the date of the enactment of this Act [
   July 4, 2025
   ].”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/