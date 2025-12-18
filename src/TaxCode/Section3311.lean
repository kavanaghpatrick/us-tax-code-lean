/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2f13f9c6-be40-482a-a816-ebd427ec2b4f
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
# IRC Section 3311 - Short title

This file formalizes IRC §3311 (Short title).

## References
- [26 USC §3311](https://www.law.cornell.edu/uscode/text/26/3311)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 3311 - Short title
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   | next
   This chapter may be cited as the “
   Federal Unemployment Tax Act
   .”
   (Aug. 16, 1954, ch. 736,
   68A Stat. 454
   , § 3308; renumbered § 3309,
   Pub. L. 86–778, title V, § 531(d)(1)
   ,
   Sept. 13, 1960
   ,
   74 Stat. 983
   ; renumbered § 3311,
   Pub. L. 91–373, title I, § 104(b)(1)
   ,
   Aug. 10, 1970
   ,
   84 Stat. 697
   .)
   Statutory Notes and Related Subsidiaries
   Short Title of 1976 Amendment
   Pub. L. 94–566, § 1
   ,
   Oct. 20, 1976
   ,
   90 Stat. 2667
   , provided that:
   “This Act [enacting
   section 603a of Title 42
   , The Public Health and Welfare, amending
   section 3304 of this title
   and provisions set out as notes under sections 3301, 3303, 3304, 3306, 3309, and 6157 of this title, sections 8501, 8503, 8504, 8505, 8506, 8521, and 8522 of Title 5, Government Organization and
   Employees,
   sections 49b and 49d of Title 29, Labor, and sections 607, 1101, 1105, 1301, 1321, 1382, 1382a, 1382d, and 1382e of Title 42, and enacting provisions set out as notes under sections 3301, 3303, 3304, and 3306 of this title, sections 8501 and 8506 of Title 5, and sections 607, 1101, 1321, 1382, 1382d, 1382e, and 1396a of Title 42] may be cited as the ‘
   Unemployment Compensation Amendments of 1976
   ’.”
   Short Title of 1975 Amendment
   Pub. L. 94–45, § 1
   ,
   June 30, 1975
   ,
   89 Stat. 236
   , provided that:
   “This Act [amending sections
   44
   and
   3302
   of this title and amending provisions set out as notes under sections
   44
   and
   3304
   of this title and enacting provisions set out as notes under sections
   3302
   and
   3304
   of this title] may be cited as the ‘Emergency
   Compensation
   and Special Unemployment Assistance Extension Act of 1975’.”
   Short Title of 1970 Amendment
   Pub. L. 91–373, § 1
   ,
   Aug. 10, 1970
   ,
   84 Stat. 695
   , provided:
   “That this Act [enacting sections
   3309
   and
   3310
   of this title and sections 504, 1106, 1107, and 1108 of Title 42, The Public Health and Welfare, repealing
   section 8524 of Title 5
   , Government Organization and
   Employees,
   and amending sections 1563, 3301 to 3306, and 6157 of this title, sections 77c and 78c of Title 15, Commerce and Trade, and sections 1101, 1102, 1103, 1105, and 1323 of Title 42, and enacting provisions set out as notes under sections 3301 to 3304, 3306, and 6157 of this title,
   section 77c of Title 15
   , and
   section 1101 of Title 42
   ] may be cited as the ‘
   Employment Security Amendments of 1970
   ’.”
   CFR Title
   Parts
   20
   601
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/