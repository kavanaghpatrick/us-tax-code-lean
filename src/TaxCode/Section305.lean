/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9d1c6027-4e3e-44c1-a98a-41eca4687f77

Aristotle encountered an error processing this file. The team has been notified.

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
# IRC Section 305 - Distributions of stock and stock rights

This file formalizes IRC §305 (Distributions of stock and stock rights).

## References
- [26 USC §305](https://www.law.cornell.edu/uscode/text/26/305)

## Summary
   Quick search by citation:
   Title
   Section
   Go!
   26 U.S. Code § 305 - Distributions of stock and stock rights
   U.S. Code
   Notes
   Authorities (CFR)
   prev
   |
   next
   (a)
   General rule
   Except as otherwise provided in this section, gross income does not include the amount of any distribution of the
   stock
   of a corporation made by such corporation to its
   shareholders
   with respect to its
   stock
   .
   (b)
   Exceptions
   Subsection (a) shall not apply to a distribution by a corporation of its
   stock
   , and the distribution shall be treated as a distribution of
   property
   to which
   section 301
   applies—
   (1)
   Distributions in lieu of money
   If the distribution is, at the election of any of the
   shareholders
   (whether exercised before or after the declaration thereof), payable either—
   (A)
   in its
   stock
   , or
   (B)
   in
   property
   .
   (2)
   Disproportionate distributions
   If the distribution (or a series of distributions of which such distribution is one) has the result of—
   (A)
   the receipt of
   property
   by some
   shareholders
   , and
   (B)
   an increase in the proportionate interests of other
   shareholders
   in the assets or earnings and profits of the corporation.
   (3)
   Distributions of common and preferred stock
   If the distribution (or a series of distributions of which such distribution is one) has the result of—
   (A)
   the receipt of preferred
   stock
   by some common
   shareholders,
   and
   (B)
   the receipt of common
   stock
   by other common
   shareholders.
   (4)
   Distributions on preferred stock
   If the distribution is with respect to preferred
   stock
   , other than an increase in the conversion ratio of convertible preferred
   stock
   made solely to take account of a
   stock
   dividend or
   stock
   split with respect to the
   stock
   into which such convertible
   stock
   is convertible.
   (5)
   Distributions of convertible preferred stock
   If the distribution is of convertible preferred
   stock
   , unless it is established to the satisfaction of the Secretary that such distribution will not have the result described in paragraph (2).
   (c)
   Certain transactions treated as distributions
   For purposes of this section and section 301, the Secretary shall prescribe regulations under which a change in conversion ratio, a change in redemption price, a difference between redemption price and issue price, a redemption which is treated as a distribution to which section 301 applies, or any transaction (including a recapitalization) having a similar effect on the interest of any
   shareholder
   shall be treated as a distribution with respect to any
   shareholder
   whose proportionate interest in the earnings and profits or assets of the corporation is increased by such change, difference, redemption, or similar transaction. Regulations prescribed under the preceding sentence shall provide that—
   (1)
   where the issuer of
   stock
   is required to redeem the
   stock
   at a specified time or the holder of
   stock
   has the option to require the issuer to redeem the
   stock
   , a redemption premium resulting from such requirement or option shall be treated as reasonable only if the amount of such premium does not exceed the amount determined under the principles of section 1273(a)(3),
   (2)
   a redemption premium shall not fail to be treated as a distribution (or series of distributions) merely because the
   stock
   is callable, and
   (3)
   in any case in which a redemption premium is treated as a distribution (or series of distributions), such premium shall be taken into account under principles similar to the principles of section 1272(a).
   (d)
   Definitions
   (1)
   Rights to acquire stock
   For purposes of this section, the term “
   stock
   ” includes rights to acquire such
   stock
   .
   (2)
   Shareholders
   For purposes of subsections (b) and (c), the term “
   shareholder
   ” includes a holder of rights or of convertible
   securities.
   (e)
   Treatment of purchaser of stripped preferred stock
   (1)
   In general
   If any person
   purchases
   after
   April 30, 1993
   , any
   stripped preferred stock,
   then such person, while holding such
   stock,
   shall include in gross income amounts equal to the amounts which would have been so includible if such
   stripped preferred stock
   were a bond issued on the
   purchase
   date and having original issue discount equal to the excess, if any, of—
   (A)
   the redemption price for such
   stock
   , over
   (B)
   the price at which such person purchased such
   stock
   .
   The preceding sentence shall also apply in the case of any person whose basis in such
   stock
   is determined by reference to the basis in the hands of such purchaser.
   (2)
   Basis adjustments
   Appropriate adjustments to basis shall be made for amounts includible in gross income under paragraph (1).
   (3)
   Tax treatment of person stripping stock
   If any person strips the rights to 1 or more dividends from any
   stock
   described in paragraph (5)(B) and after
   April 30, 1993
   , disposes of such dividend rights, for purposes of paragraph (1), such person shall be treated as having purchased the
   stripped preferred stock
   on the date of such
   disposition
   for a
   purchase
   price equal to such person’s adjusted basis in such
   stripped preferred stock.
   (4)
   Amounts treated as ordinary income
   Any amount included in gross income under paragraph (1) shall be treated as ordinary income.
   (5)
   Stripped preferred stock
   For purposes of this subsection—
   (A)
   In general
   The term “
   stripped preferred stock
   ” means any
   stock
   described in subparagraph (B) if there has been a separation in ownership between such
   stock
   and any dividend on such
   stock
   which has not become payable.
   (B)
   Description of stock
   Stock is described in this subsection if such
   stock
   —
   (i)
   is limited and preferred as to dividends and does not participate in corporate growth to any significant extent, and
   (ii)
   has a fixed redemption price.
   (6)
   Purchase
   For purposes of this subsection, the term “
   purchase
   ” means—
   (A)
   any acquisition of
   stock
   , where
   (B)
   the basis of such
   stock
   is not determined in whole or in part by the reference to the adjusted basis of such
   stock
   in the hands of the person from whom acquired.
   (7)
   Cross reference
   For treatment of stripped interests in certain accounts or entities holding preferred
   stock
   , see section 1286(e).
   (f)
   Cross references
   For special rules—
   (1)
   Relating to the receipt of
   stock
   and
   stock
   rights in corporate organizations and reorganizations, see part III (sec. 351 and following).
   (2)
   In the case of a distribution which results in a gift, see section 2501 and following.
   (3)
   In the case of a distribution which has the effect of the payment of compensation, see section 61(a)(1).
   (Aug. 16, 1954, ch. 736,
   68A Stat. 90
   ;
   Pub. L. 91–172, title IV, § 421(a)
   ,
   Dec. 30, 1969
   ,
   83 Stat. 614
   ;
   Pub. L. 94–455, title XIX, § 1906(b)(13)(A)
   ,
   Oct. 4, 1976
   ,
   90 Stat. 1834
   ;
   Pub. L. 97–34, title III, § 321(a)
   , (b),
   Aug. 13, 1981
   ,
   95 Stat. 287
   , 289;
   Pub. L. 97–448, title I, § 103(f)
   ,
   Jan. 12, 1983
   ,
   96 Stat. 2378
   ;
   Pub. L. 101–508, title XI
   , §§ 11322(a), 11801(a)(17), (c)(7),
   Nov. 5, 1990
   ,
   104 Stat. 1388–463
   , 1388–521, 1388–524;
   Pub. L. 103–66, title XIII, § 13206(c)(1)
   ,
   Aug. 10, 1993
   ,
   107 Stat. 465
   ;
   Pub. L. 108–357, title VIII, § 831(b)
   ,
   Oct. 22, 2004
   ,
   118 Stat. 1587
   ;
   Pub. L. 115–141, div. U, title IV, § 401(c)(2)(D)
   ,
   Mar. 23, 2018
   ,
   132 Stat. 1206
   .)


-/
-- TODO: Add type definitions
-- TODO: Add main functions