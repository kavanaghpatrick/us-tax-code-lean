/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8b301de1-6174-4eb8-8df0-0650213b5dc5
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

structure TaxYear where year : Nat

; h_valid : year ≥ 1913; deriving

DecidableEq, Repr
inductive FilingStatus | Single | MarriedFilingJointly | MarriedFilingSeparately | HeadOfHousehold | QualifyingWidower | Estate | Trust deriving Repr, DecidableEq, Inhabited

/-!
# IRC Section 1055 - Redeemable ground rents

This file formalizes IRC §1055 (Redeemable ground rents).

## References
- [26 USC §1055](https://www.law.cornell.edu/uscode/text/26/1055)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1055 - Redeemable ground rents
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Character
   For purposes of this subtitle—
   (1)
   a
   redeemable ground rent
   shall be treated as being in the nature of a mortgage, and
   (2)
   real property held subject to liabilities under a
   redeemable ground rent
   shall be treated as held subject to liabilities under a mortgage.
   (b)
   Application of subsection (a)
   (1)
   In general
   Subsection (a) shall take effect on the day after the date of the enactment of this section and shall apply with respect to taxable years ending after such date of enactment.
   (2)
   Basis of holder
   In determining the basis of real property held subject to liabilities under a
   redeemable ground rent
   , subsection (a) shall apply whether such real property was acquired before or after the enactment of this section.
   (3)
   Basis of reserved redeemable ground rent
   In the case of a
   redeemable ground rent
   reserved or created on or before the date of the enactment of this section in connection with a transfer of the right to hold real property subject to liabilities under such ground rent, the basis of such ground rent after such date in the hands of the person who reserved or created the ground rent shall be the amount taken into account in respect of such ground rent for Federal income tax purposes as consideration for the
   disposition
   of such real property. If no such amount was taken into account, such basis shall be determined as if this section had not been enacted.
   (c)
   Redeemable ground rent defined
   For purposes of this subtitle, the term “
   redeemable ground rent
   ” means only a ground rent with respect to which—
   (1)
   there is a lease of land which is assignable by the lessee without the consent of the lessor and which (together with periods for which the lease may be renewed at the option of the lessee) is for a term in excess of 15 years,
   (2)
   the leaseholder has a present or future right to terminate, and to acquire the entire interest of the lessor in the land, by payment of a determined or determinable amount, which right exists by virtue of State or local law and not because of any private agreement or privately created condition, and
   (3)
   the lessor’s interest in the land is primarily a security interest to protect the rental payments to which the lessor is entitled under the lease.
   (d)
   Cross reference
   For treatment of rentals under
   redeemable ground rents
   as interest, see section 163(c).
   (Added
   Pub. L. 88–9, § 1(b)
   ,
   Apr. 10, 1963
   ,
   77 Stat. 7
   .)
   Editorial Notes
   References in Text
   Date of the enactment of this section, referred to in subsec. (b)(1), (3), means
   Apr. 10, 1963
   , the date of approval of
   Pub. L. 88–9
   .
   Prior Provisions
   A prior
   section 1055
   was renumbered
   section 1063 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date
   Pub. L. 88–9, § 2
   ,
   Apr. 10, 1963
   ,
   77 Stat. 8
   , provided that:
   “The amendments made by subsection (a) of the first section of this Act [amending
   section 163 of this title
   ] shall take effect as of
   January 1, 1962
   , and shall apply with respect to taxable years ending on or after such date. The amendments made by subsection (b) of the first section of this Act [enacting this section] shall take effect on the day after the date of the enactment of this Act [
   Apr. 10, 1963
   ] and shall apply with respect to taxable years ending after such date of enactment.”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/