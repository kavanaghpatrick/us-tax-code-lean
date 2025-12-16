/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: abfbe851-3a86-4071-a73e-e5f52672ce0b
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
# IRC Section 895 - Income derived by a foreign central bank of issue from obligations of the United States or from bank deposits

This file formalizes IRC §895 (Income derived by a foreign central bank of issue from obligations of the United States or from bank deposits).

## References
- [26 USC §895](https://www.law.cornell.edu/uscode/text/26/895)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 895 - Income derived by a foreign central bank of issue from obligations of the United States or from bank deposits
   U.S. Code
   Notes
   prev
   |
   next
   Income derived by a foreign central bank of issue from obligations of the United States or of any agency or instrumentality thereof (including beneficial interests, participations, and other instruments issued under section 302(c) of the
   Federal National Mortgage Association Charter Act
   (
   12 U.S.C. 1717
   )) which are owned by such foreign central bank of issue, or derived from interest on deposits with persons carrying on the banking business, shall not be included in gross income and shall be exempt from taxation under this subtitle unless such obligations or deposits are held for, or used in connection with, the conduct of commercial banking functions or other commercial activities. For purposes of the preceding sentence the Bank for International Settlements shall be treated as a foreign central bank of issue.
   (Added
   Pub. L. 87–29, § 1(a)
   ,
   May 4, 1961
   ,
   75 Stat. 64
   ; amended
   Pub. L. 89–809, title I, § 102(a)(4)(A)
   ,
   Nov. 13, 1966
   ,
   80 Stat. 1543
   .)
   Editorial Notes
   Amendments
   1966—
   Pub. L. 89–809
   exempted income derived from obligations of agencies or instrumentalities of the United States and income derived from interest on deposits with persons carrying on the banking business, inserted “(including beneficial interests, participations, and other instruments issued under section 302(c) of the
   Federal National Mortgage Association Charter Act
   (
   12 U.S.C. 1717
   )),” and inserted sentence requiring the Bank for International Settlements to be treated as a foreign central bank of issue.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1966 Amendment
   Amendment by
   Pub. L. 89–809
   applicable with respect to taxable years beginning after
   Dec. 31, 1966
   , except that in applying
   section 864(c)(4)(B)(iii) of this title
   with respect to a binding contract entered into on or before
   Feb. 24, 1966
   , activities in the United States on or before such date in negotiating or carrying out such contract shall not be taken into account, see
   section 102(e)(1) of Pub. L. 89–809
   , set out as a note under
   section 861 of this title
   .
   Effective Date
   Pub. L. 87–29, § 1(c)
   ,
   May 4, 1961
   ,
   75 Stat. 64
   , provided that:
   “The amendments made by subsections (a) and (b) [enacting this section and amending analysis preceding
   section 891 of this title
   ] shall be effective with respect to income received in taxable years beginning after
   December 31, 1960
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/