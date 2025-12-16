/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 28b7f66c-d87d-46cb-8b1b-9f4c3d7167ef
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
# IRC Section 502 - Feeder organizations

This file formalizes IRC §502 (Feeder organizations).

## References
- [26 USC §502](https://www.law.cornell.edu/uscode/text/26/502)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 502 - Feeder organizations
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   An organization operated for the primary purpose of carrying on a trade or business for profit shall not be exempt from taxation under
   section 501
   on the ground that all of its profits are payable to one or more organizations exempt from taxation under section 501.
   (b)
   Special rule
   For purposes of this section, the term “trade or business” shall not include—
   (1)
   the deriving of rents which would be excluded under section 512(b)(3), if
   section 512
   applied to the organization,
   (2)
   any trade or business in which substantially all the work in carrying on such trade or business is performed for the organization without compensation, or
   (3)
   any trade or business which is the selling of merchandise, substantially all of which has been received by the organization as gifts or contributions.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 166
   ;
   Pub. L. 91–172, title I, § 121(b)(7)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 542
   .)
   Editorial Notes
   Amendments
   1969—
   Pub. L. 91–172
   redesignated first sentence of existing provisions as subsec. (a), and substantial portion of second sentence as subsec. (b)(1), and, in subsec. (b)(1) as so redesignated, inserted reference to
   section 512 of this title
   , and added pars. (2) and (3).
   Statutory Notes and Related Subsidiaries
   Effective Date of 1969 Amendment
   Amendment by
   Pub. L. 91–172
   applicable to taxable years beginning after
   Dec. 31, 1969
   , see
   section 121(g) of Pub. L. 91–172
   , set out as a note under
   section 511 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/

-- TODO: Add type definitions

-- TODO: Add main functions

-- TODO: Add theorems to prove

-- Example usage
#eval "Section loaded"