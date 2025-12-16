/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6aa1c8d0-9760-444b-99b1-f3b3e2a81e74
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
# IRC Section 2016 - Recovery of taxes claimed as credit

This file formalizes IRC §2016 (Recovery of taxes claimed as credit).

## References
- [26 USC §2016](https://www.law.cornell.edu/uscode/text/26/2016)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 2016 - Recovery of taxes claimed as credit
   U.S. Code
   Notes
   prev
   | next
   If any tax claimed as a credit under section 2014 is recovered from any foreign country, the executor, or any other person or persons recovering such amount, shall give notice of such recovery to the Secretary at such time and in such manner as may be required by regulations prescribed by him, and the Secretary shall (despite the provisions of section 6501) redetermine the amount of the tax under this chapter and the amount, if any, of the tax due on such redetermination, shall be paid by the executor or such person or persons, as the case may be, on notice and demand. No interest shall be assessed or collected on any amount of tax due on any redetermination by the Secretary resulting from a refund to the executor of tax claimed as a credit under section 2014, for any period before the receipt of such refund, except to the extent interest was paid by the foreign country on such refund.
   (Aug. 16, 1954, ch. 736,
   68A Stat. 380
   ;
   Pub. L. 94–455, title XIX
   , §§ 1902(a)(12)(C), 1906(b)(13)(A),
   Oct. 4, 1976
   ,
   90 Stat. 1806
   , 1834;
   Pub. L. 107–16, title V, § 532(c)(4)
   ,
   June 7, 2001
   ,
   115 Stat. 74
   ;
   Pub. L. 107–147, title IV, § 411(h)
   ,
   Mar. 9, 2002
   ,
   116 Stat. 46
   .)
   Editorial Notes
   Amendments
   2002—
   Pub. L. 107–147
   struck out “any State, any possession of the United States, or the District of Columbia,” after “any foreign country,”.
   2001—
   Pub. L. 107–16
   struck out “2011 or” before “2014 is recovered”.
   1976—
   Pub. L. 94–455
   struck out “Territory or” after “any State, any” and “or his delegate” after “Secretary”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 2002 Amendment
   Amendment by
   Pub. L. 107–147
   effective as if included in the provisions of the
   Economic Growth and Tax Relief Reconciliation Act of 2001
   ,
   Pub. L. 107–16
   , to which such amendment relates, see
   section 411(x) of Pub. L. 107–147
   , set out as a note under
   section 25B of this title
   .
   Effective Date of 2001 Amendment
   Amendment by
   Pub. L. 107–16
   applicable to estates of decedents dying, and generation-skipping transfers, after
   Dec. 31, 2004
   , see
   section 532(d) of Pub. L. 107–16
   , set out as a note under
   section 2012 of this title
   .
   Effective Date of 1976 Amendment
   Amendment by
   section 1902(a)(12)(C) of Pub. L. 94–455
   applicable to estates of decedents dying after
   Oct. 4, 1976
   , see
   section 1902(c)(1) of Pub. L. 94–455
   , set out as a note under
   section 2012 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/