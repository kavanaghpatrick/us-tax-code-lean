/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 13b8b5de-cd0d-44a9-a291-a5a57e3d5261
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
# IRC Section 1236 - Dealers in securities

This file formalizes IRC §1236 (Dealers in securities).

## References
- [26 USC §1236](https://www.law.cornell.edu/uscode/text/26/1236)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 1236 - Dealers in securities
   U.S. Code
   Notes
   prev
   |
   next
   (a)
   Capital gains
   Gain by a dealer in securities from the sale or exchange of any
   security
   shall in no event be considered as gain from the sale or exchange of a capital asset unless—
   (1)
   the
   security
   was, before the close of the day on which it was acquired (or such earlier time as the Secretary may prescribe by regulations), clearly identified in the dealer’s records as a
   security
   held for investment; and
   (2)
   the
   security
   was not, at any time after the close of such day (or such earlier time), held by such dealer primarily for sale to customers in the ordinary course of his trade or business.
   (b)
   Ordinary losses
   Loss by a dealer in securities from the sale or exchange of any
   security
   shall, except as otherwise provided in section 582(c), (relating to bond, etc., losses of banks), in no event be considered as ordinary loss if at any time the
   security
   was clearly identified in the dealer’s records as a
   security
   held for investment.
   (c)
   Definition of security
   For purposes of this section, the term “
   security
   ” means any share of
   stock
   in any corporation, certificate of
   stock
   or interest in any corporation, note, bond, debenture, or evidence of indebtedness, or any evidence of an interest in or right to subscribe to or purchase any of the foregoing.
   (d)
   Special rule for floor specialists
   (1)
   In general
   In the case of a
   floor specialist
   (but only with respect to acquisitions, in connection with his duties on an exchange, of
   stock
   in which the specialist is registered with the exchange), subsection (a) shall be applied—
   (A)
   by inserting “the 7th business day following” before “the day” the first place it appears in paragraph (1) and by inserting “7th business” before “day” in paragraph (2), and
   (B)
   by striking the parenthetical phrase in paragraph (1).
   (2)
   Floor specialist
   The term “
   floor specialist
   ” means a person who is—
   (A)
   a member of a national securities exchange,
   (B)
   is registered as a specialist with the exchange, and
   (C)
   meets the requirements for specialists established by the
   Securities and Exchange Commission
   .
   (e)
   Special rule for options
   For purposes of subsection (a), any
   security
   acquired by a dealer pursuant to an
   option
   held by such dealer may be treated as held for investment only if the dealer, before the close of the day on which the
   option
   was acquired, clearly identified the
   option
   on his records as held for investment. For purposes of the preceding sentence, the term
   “option”
   includes the right to subscribe to or purchase any
   security
   .
   (Aug. 16, 1954, ch. 736,
   68A Stat. 330
   ;
   Pub. L. 94–455, title XIX, § 1901(b)(3)(E)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1793
   ;
   Pub. L. 97–34, title V, § 506
   ,
   Aug. 13, 1981
   ,
   95 Stat. 332
   ;
   Pub. L. 97–448, title I, § 105(d)(1)
   ,
   Jan. 12, 1983
   ,
   96 Stat. 2387
   ;
   Pub. L. 98–369, div. A, title I, § 107(b)
   ,
   July 18, 1984
   ,
   98 Stat. 630
   ;
   Pub. L. 113–295, div. A, title II, § 221(a)(83)
   ,
   Dec. 19, 2014
   ,
   128 Stat. 4049
   .)
   Editorial Notes
   Amendments
   2014—Subsec. (b).
   Pub. L. 113–295
   struck out “after
   November 19, 1951
   ,” after “time”.
   1984—Subsec. (a)(1).
   Pub. L. 98–369, § 107(b)(1)
   , substituted “the
   security
   was, before the close of the day on which it was acquired (or such earlier time as the Secretary may prescribe by regulations), clearly identified in the dealer’s records as a
   security
   held for investment; and” for “the
   security
   was, before the close of the day on which it was acquired (before the close of the following day in the case of an acquisition before
   January 1, 1982
   ), clearly identified in the dealer’s records as a
   security
   held for investment or if acquired before
   October 20, 1951
   , was so identified before
   November 20, 1951
   ; and”.
   Subsec. (a)(2).
   Pub. L. 98–369, § 107(b)(2)
   , inserted “(or such earlier time)” after “such day”.
   1983—Subsec. (e).
   Pub. L. 97–448
   added subsec. (e).
   1981—Subsec. (a).
   Pub. L. 97–34, § 506(a)
   , substituted “before the close of the day on which it was acquired (before the close of the following day in the case of an acquisition before
   January 1, 1982
   )” for “before the expiration of the 30th day after the date of its acquisition” in par. (1) and “close of such day” for “expiration of such 30th day” in par. (2).
   Subsec. (d).
   Pub. L. 97–34, § 506(b)
   , added subsec. (d).
   1976—Subsec. (b).
   Pub. L. 94–455
   substituted “ordinary loss” for “loss from the sale or exchange of
   property
   which is not a capital asset”.
   Statutory Notes and Related Subsidiaries
   Effective Date of 2014 Amendment
   Amendment by
   Pub. L. 113–295
   effective
   Dec. 19, 2014
   , subject to a savings provision, see
   section 221(b) of Pub. L. 113–295
   , set out as a note under
   section 1 of this title
   .
   Effective Date of 1984 Amendment
   Amendment by
   Pub. L. 98–369
   applicable to positions entered into after
   July 18, 1984
   , in taxable years ending after that date, see
   section 107(e) of Pub. L. 98–369
   , set out as a note under
   section 1092 of this title
   .
   Effective Date of 1983 Amendment
   Pub. L. 97–448, title I, § 105(d)(2)
   ,
   Jan. 12, 1983
   ,
   96 Stat. 2387
   , provided that:
   “The amendment made by paragraph (1) [amending this section] shall apply to securities acquired after
   September 22, 1982
   , in taxable years ending after such date.”
   Effective Date of 1981 Amendment
   Amendment by
   Pub. L. 97–34
   applicable to
   property
   acquired by the taxpayer after
   Aug. 13, 1981
   , in taxable years ending after such date, and applicable when so elected with respect to
   property
   held on
   June 23, 1981
   , see
   section 508 of Pub. L. 97–34
   , set out as an Effective Date note under
   section 1092 of this title
   .
   Effective Date of 1976 Amendment
   Amendment by
   Pub. L. 94–455
   applicable with respect to taxable years beginning after
   Dec. 31, 1976
   , see
   section 1901(d) of Pub. L. 94–455
   , set out as a note under
   section 2 of this title
   .
   U.S. Code Toolbox
   Law about... Articles from Wex
   Table of Popular Names
   Parallel Table of Authorities
   How
   current is this?
-/