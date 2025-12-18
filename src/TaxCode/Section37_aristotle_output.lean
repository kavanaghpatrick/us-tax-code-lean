/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dcc1431f-587e-44ac-b2e9-318a2379fd91
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3f677ccc-14c6-416d-9d9c-8bf957c6668b
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

structure TaxYear where year : Nat

; h_valid : year ≥ 1913; deriving

DecidableEq, Repr
inductive FilingStatus | Single | MarriedFilingJointly | MarriedFilingSeparately | HeadOfHousehold | QualifyingWidower | Estate | Trust deriving Repr, DecidableEq, Inhabited

/-!
# IRC Section 37 - Overpayments of tax

This file formalizes IRC §37 (Overpayments of tax).

## References
- [26 USC §37](https://www.law.cornell.edu/uscode/text/26/37)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 37 - Overpayments of tax
   U.S. Code
   Notes
   prev
   | next
   For credit against the tax imposed by this subtitle for overpayments of tax, see section 6401.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 16
   , § 38; renumbered § 39,
   Pub. L. 87–834, § 2(a)
   ,
   Oct. 16, 1962
   ,
   76 Stat. 962
   ; renumbered § 40,
   Pub. L. 89–44, title VIII, § 809(c)
   ,
   June 21, 1965
   ,
   79 Stat. 167
   ; renumbered § 42,
   Pub. L. 92–178, title VI, § 601(a)
   ,
   Dec. 10, 1971
   ,
   85 Stat. 553
   ; renumbered § 43,
   Pub. L. 94–12, title II, § 203(a)
   ,
   Mar. 29, 1975
   ,
   89 Stat. 29
   ; renumbered § 44,
   Pub. L. 94–12, title II, § 204(a)
   ,
   Mar. 29, 1975
   ,
   89 Stat. 30
   ; renumbered § 45,
   Pub. L. 94–12, title II, § 208(a)
   ,
   Mar. 29, 1975
   ,
   89 Stat. 32
   ; renumbered § 35,
   Pub. L. 98–369, div. A, title IV, § 471(c)
   ,
   July 18, 1984
   ,
   98 Stat. 826
   ; renumbered § 36,
   Pub. L. 107–210, div. A, title II, § 201(a)
   ,
   Aug. 6, 2002
   ,
   116 Stat. 954
   ; renumbered § 37,
   Pub. L. 110–289, div. C, title I, § 3011(a)
   ,
   July 30, 2008
   ,
   122 Stat. 2888
   .)
   Editorial Notes
   Prior Provisions
   A prior
   section 37
   was renumbered
   section 22 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/