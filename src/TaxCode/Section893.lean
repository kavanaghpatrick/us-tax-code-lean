/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: fffab652-d731-4437-b913-07c4e195263d
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
# IRC Section 893 - Compensation of employees of foreign governments or international organizations

This file formalizes IRC §893 (Compensation of employees of foreign governments or international organizations).

## References
- [26 USC §893](https://www.law.cornell.edu/uscode/text/26/893)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 893 - Compensation of employees of foreign governments or international organizations
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Rule for exclusion
   Wages, fees, or salary of any employee of a foreign government or of an international organization (including a consular or other officer, or a nondiplomatic representative), received as compensation for official services to such government or international organization shall not be included in gross income and shall be exempt from taxation under this subtitle if—
   (1)
   such employee is not a citizen of the United States, or is a citizen of the Republic of the Philippines (whether or not a citizen of the United States); and
   (2)
   in the case of an employee of a foreign government, the services are of a character similar to those performed by employees of the Government of the United States in foreign countries; and
   (3)
   in the case of an employee of a foreign government, the foreign government grants an equivalent exemption to employees of the Government of the United States performing similar services in such foreign country.
   (b)
   Certificate by Secretary of State
   The Secretary of State shall certify to the Secretary of the Treasury the names of the foreign countries which grant an equivalent exemption to the employees of the Government of the United States performing services in such foreign countries, and the character of the services performed by employees of the Government of the United States in foreign countries.
   (c)
   Limitation on exclusion
   Subsection (a) shall not apply to—
   (1)
   any employee of a
   controlled commercial entity
   (as defined in
   section 892(a)(2)(B)
   ), or
   (2)
   any employee of a foreign government whose services are primarily in connection with a commercial activity (whether within or outside the United States) of the foreign government.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 284
   ;
   Pub. L. 100–647, title I, § 1012(t)(4)
   ,
   Nov. 10, 1988
   ,
   102 Stat. 3527
   .)
   Editorial Notes
   Amendments
   1988—Subsec. (c).
   Pub. L. 100–647
   added subsec. (c).
   Statutory Notes and Related Subsidiaries
   Effective Date of 1988 Amendment
   Amendment by
   Pub. L. 100–647
   effective, except as otherwise provided, as if included in the provision of the
   Tax Reform Act of 1986
   ,
   Pub. L. 99–514
   , to which such amendment relates, see
   section 1019(a) of Pub. L. 100–647
   , set out as a note under
   section 1 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/