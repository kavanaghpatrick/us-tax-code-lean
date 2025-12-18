/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f0686f45-284b-474c-881b-e2b4b015e897
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
# IRC Section 2037 - Transfers taking effect at death

This file formalizes IRC §2037 (Transfers taking effect at death).

## References
- [26 USC §2037](https://www.law.cornell.edu/uscode/text/26/2037)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2037 - Transfers taking effect at death
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   The value of the gross estate shall include the value of all property to the extent of any interest therein of which the decedent has at any time after
   September 7, 1916
   , made a transfer (except in case of a bona fide sale for an adequate and full consideration in money or money’s worth), by trust or otherwise, if—
   (1)
   possession or enjoyment of the property can, through ownership of such interest, be obtained only by surviving the decedent, and
   (2)
   the decedent has retained a
   reversionary interest
   in the property (but in the case of a transfer made before
   October 8, 1949
   , only if such
   reversionary interest
   arose by the express terms of the instrument of transfer), and the value of such
   reversionary interest
   immediately before the death of the decedent exceeds 5 percent of the value of such property.
   (b)
   Special rules
   For purposes of this section, the term “
   reversionary interest
   ” includes a possibility that property transferred by the decedent—
   (1)
   may return to him or his estate, or
   (2)
   may be subject to a power of disposition by him,
   but such term does not include a possibility that the income alone from such property may return to him or become subject to a power of disposition by him. The value of a
   reversionary interest
   immediately before the death of the decedent shall be determined (without regard to the fact of the decedent’s death) by usual methods of valuation, including the use of tables of mortality and actuarial principles, under regulations prescribed by the Secretary. In determining the value of a possibility that property may be subject to a power of disposition by the decedent, such possibility shall be valued as if it were a possibility that such property may return to the decedent or his estate. Notwithstanding the foregoing, an interest so transferred shall not be included in the decedent’s gross estate under this section if possession or enjoyment of the property could have been obtained by any beneficiary during the decedent’s life through the exercise of a
   general power of appointment
   (as defined in
   section 2041
   ) which in fact was exercisable immediately before the decedent’s death.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 382
   ;
   Pub. L. 87–834, § 18(a)(2)(E)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 1052
   ;
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1834
   .)
   Editorial Notes
   Amendments
   1976—Subsec. (b).
   Pub. L. 94–455
   struck out “or his delegate” after “Secretary”.
   1962—Subsec. (a).
   Pub. L. 87–834
   struck out provisions which excepted real property situated outside of the United States.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1962 Amendment
   Amendment by
   Pub. L. 87–834
   applicable to estates of decedents dying after
   Oct. 16, 1962
   , except as otherwise provided, see
   section 18(b) of Pub. L. 87–834
   , set out as a note under
   section 2031 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/