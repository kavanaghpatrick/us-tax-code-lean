/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f70208cb-9d3b-45fb-a3cc-64e05383f01d
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
# IRC Section 1071 - Repealed. Pub. L. 104–7, § 2(a), Apr. 11, 1995, 109 Stat. 93]

This file formalizes IRC §1071 (Repealed. Pub. L. 104–7, § 2(a), Apr. 11, 1995, 109 Stat. 93]).

## References
- [26 USC §1071](https://www.law.cornell.edu/uscode/text/26/1071)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1071 - Repealed. Pub. L. 104–7, § 2(a), Apr. 11, 1995, 109 Stat. 93]
   U.S. Code
   Notes
   Section, acts Aug. 16, 1954, ch. 736,
   68A Stat. 311
   ;
   Sept. 2, 1958
   ,
   Pub. L. 85–866, title I, § 48(a)
   ,
   72 Stat. 1642
   ;
   Oct. 4, 1976
   ,
   Pub. L. 94–455, title XIX
   , §§ 1901(b)(31)(E), 1906(b)(13)(A),
   90 Stat. 1800
   , 1834, provided for nonrecognition on FCC certified sales and exchanges.
   Statutory Notes and Related Subsidiaries
   Effective Date of Repeal
   Pub. L. 104–7, § 2(d)
   ,
   Apr. 11, 1995
   ,
   109 Stat. 93
   , provided that:
   “(1)
   In general.—
   The amendments made by this section [repealing this section and amending sections
   1245
   and
   1250
   of this title] shall apply to—
   “(A)
   sales and exchanges on or after
   January 17, 1995
   , and
   “(B)
   sales and exchanges before such date if the FCC tax certificate with respect to such sale or exchange is issued on or after such date.
   “(2)
   Binding contracts.—
   “(A)
   In general.—
   The amendments made by this section shall not apply to any sale or exchange pursuant to a written contract which was binding on
   January 16, 1995
   , and at all times thereafter before the sale or exchange, if the FCC tax certificate with respect to such sale or exchange was applied for, or issued, on or before such date.
   “(B)
   Sales contingent on issuance of certificate.—
   “(i)
   In general.—
   A contract shall be treated as not binding for purposes of subparagraph (A) if the sale or exchange pursuant to such contract, or the material terms of such contract, were contingent, at any time on
   January 16, 1995
   , on the issuance of an FCC tax certificate. The preceding sentence shall not apply if the FCC tax certificate for such sale or exchange is issued on or before
   January 16, 1995
   .
   “(ii)
   Material terms.—
   For purposes of clause (i), the material terms of a contract shall not be treated as contingent on the issuance of an FCC tax certificate solely because such terms provide that the sales price would, if such certificate were not issued, be increased by an amount not greater than 10 percent of the sales price otherwise provided in the contract.
   “(3)
   FCC tax certificate.—
   For purposes of this subsection, the term ‘FCC tax certificate’ means any certificate of the
   Federal Communications Commission
   for the effectuation of section 1071 of the
   Internal Revenue Code of 1986
   (as in effect on the day before the date of the enactment of this Act [
   Apr. 11, 1995
   ]).”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/