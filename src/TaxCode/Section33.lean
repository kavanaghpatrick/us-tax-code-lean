/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8542bd41-9997-4b43-91a5-54b360acc9c0
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b9b40bd3-65bd-48f4-8390-de2955d24583
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token ';'; expected command
unexpected identifier; expected 'instance'-/
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
# IRC Section 33 - Tax withheld at source on nonresident aliens and foreign corporations

This file formalizes IRC §33 (Tax withheld at source on nonresident aliens and foreign corporations).

## References
- [26 USC §33](https://www.law.cornell.edu/uscode/text/26/33)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 33 - Tax withheld at source on nonresident aliens and foreign corporations
   U.S. Code
   Notes
   prev
   |
   next
   There shall be allowed as a credit against the tax imposed by this subtitle the amount of tax withheld at source under subchapter A of chapter 3 (relating to withholding of tax on nonresident aliens and on foreign corporations).
   (Aug. 16, 1954, ch. 736,
   68A Stat. 13
   , § 32; renumbered § 33 and amended
   Pub. L. 98–369, div. A, title IV
   , §§ 471(c), 474(j),
   July 18, 1984
   ,
   98 Stat. 826
   , 832.)
   Editorial Notes
   Prior Provisions
   A prior
   section 33
   was renumbered
   section 27 of this title
   .
   Amendments
   1984—
   Pub. L. 98–369, § 471(c)
   , renumbered
   section 32 of this title
   as this section.
   Pub. L. 98–369, § 474(j)
   , amended section generally, striking out “and on tax-free covenant bonds” after “foreign corporations” in section catchline, and, in text, substituting “as a credit against the tax imposed by this subtitle” for “as credits against the tax imposed by this chapter”, and striking out designation “(1)” before “the amount of tax withheld”, and “, and (2) the amount of tax withheld at source under subchapter B of chapter 3 (relating to interest on tax-free covenant bonds)” after “on foreign corporations)”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 1984 Amendment
   Pub. L. 98–369, div. A, title IV, § 475(b)
   ,
   July 18, 1984
   ,
   98 Stat. 847
   , provided that:
   “The amendments made by subsections (j) and (r)(29) [amending this section and sections
   12
   ,
   164
   ,
   1441
   ,
   1442
   ,
   6049
   , and
   7701
   of this title and repealing
   section 1451 of this title
   ] shall not apply with respect to obligations issued before
   January 1, 1984
   .”
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/