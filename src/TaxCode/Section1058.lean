/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d0cb9f60-c13c-42ab-9dc6-c289f253c31d
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
# IRC Section 1058 - Transfers of securities under certain agreements

This file formalizes IRC §1058 (Transfers of securities under certain agreements).

## References
- [26 USC §1058](https://www.law.cornell.edu/uscode/text/26/1058)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1058 - Transfers of securities under certain agreements
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   General rule
   In the case of a taxpayer who transfers securities (as defined in
   section 1236(c)
   ) pursuant to an agreement which meets the requirements of subsection (b), no gain or loss shall be recognized on the exchange of such securities by the taxpayer for an obligation under such agreement, or on the exchange of rights under such agreement by that taxpayer for securities identical to the securities transferred by that taxpayer.
   (b)
   Agreement requirements
   In order to meet the requirements of this subsection, an agreement shall—
   (1)
   provide for the return to the transferor of securities identical to the securities transferred;
   (2)
   require that payments shall be made to the transferor of amounts equivalent to all interest, dividends, and other distributions which the owner of the securities is entitled to receive during the period beginning with the transfer of the securities by the transferor and ending with the transfer of identical securities back to the transferor;
   (3)
   not reduce the risk of loss or opportunity for gain of the transferor of the securities in the securities transferred; and
   (4)
   meet such other requirements as the Secretary may by regulation prescribe.
   (c)
   Basis
   Property acquired by a taxpayer described in subsection (a), in a transaction described in that subsection, shall have the same basis as the property transferred by that taxpayer.
   (Added
   Pub. L. 95–345, § 2(d)(1)
   ,
   Aug. 15, 1978
   ,
   92 Stat. 482
   .)
   Editorial Notes
   Prior Provisions
   A prior
   section 1058
   was renumbered
   section 1063 of this title
   .
   Statutory Notes and Related Subsidiaries
   Effective Date
   Section applicable with respect to amounts received after
   Dec. 31, 1976
   , as payments with respect to securities loans (as defined in
   section 512(a)(5) of this title
   ), and transfers of securities, under agreements described in this section, occurring after such date, see
   section 2(e) of Pub. L. 95–345
   , set out as an Effective Date of 1978 Amendment note under
   section 509 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/