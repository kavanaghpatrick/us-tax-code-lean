/-
FINAL SEARCH: Tax-Free Compounding + Access + Control

Based on our formalized sections, find the BEST legal structure.
Eliminating strategies that don't actually work.
-/

import Mathlib

/-!
## STRATEGIES THAT ACTUALLY WORK
-/

-- Strategy 1: Buy-Borrow-Die (Simplest)
-- Uses: §1014 (step-up)
def buyBorrowDie : String := "
STRATEGY: BUY-BORROW-DIE
═══════════════════════════════════════════════════════
SETUP:
  1. Buy and hold appreciating assets (stocks, RE, etc.)
  2. NEVER sell

COMPOUNDING:
  - Unrealized gains grow tax-free
  - No tax until sale (which never happens)
  - Score: 10/10

ACCESS:
  - Borrow against portfolio (margin, PAL, SBLOC)
  - Banks lend 50-70% of portfolio value
  - Interest ~5-7%, may be deductible
  - Score: 8/10

CONTROL:
  - You own everything outright
  - Full investment discretion
  - Score: 10/10

EXIT:
  - At death: §1014 step-up erases all gains
  - Heirs inherit at FMV basis
  - Loan repaid from estate

NUMBERS ($10M portfolio, 20% basis, 20 years):
  - Ending value: ~$46M (at 8%)
  - Unrealized gain: ~$38M
  - Tax if sold: $9M (23.8%)
  - Tax at death: $0
  - Borrow capacity: $25-30M over time

VERDICT: Simple, legal, effective. Best for most people.
═══════════════════════════════════════════════════════
"

-- Strategy 2: IDGT + Installment Sale
-- Uses: §675 (swap power), §671 (grantor trust), Rev Rul 85-13
def idgtInstallment : String := "
STRATEGY: IDGT + INSTALLMENT SALE + BORROW
═══════════════════════════════════════════════════════
SETUP:
  1. Create irrevocable trust with §675 swap power (IDGT)
  2. Seed with 10% of value ($1M) as gift
  3. Sell $9M appreciated stock to trust for installment note
  4. Note pays AFR interest (~4-5%)

WHY NO GAIN ON SALE:
  - Rev. Rul. 85-13: Grantor and grantor trust are same taxpayer
  - Sale to yourself = no taxable event
  - This is ESTABLISHED law, not a loophole

COMPOUNDING:
  - Trust invests the $9M
  - You pay income tax on trust earnings (not a gift!)
  - Trust compounds at FULL pre-tax rate
  - Score: 10/10

ACCESS:
  - You hold $9M installment note
  - Pledge note as collateral → borrow $6-7M
  - Trust pays you interest on note
  - Score: 8/10

CONTROL:
  - Swap power: exchange assets with trust (equal value)
  - Can 'rescue' assets if trust underperforms
  - Trustee is independent, but you pick them
  - Score: 8/10

EXIT:
  - Trust assets pass to beneficiaries (no estate tax if planned right)
  - Note: complex rules if you die holding note

NUMBERS ($10M portfolio, 20% basis, 20 years):
  - Trust ending value: ~$46M
  - Tax you paid for trust: ~$8M (wealth transfer!)
  - Your note value: $9M (can borrow against)
  - Estate tax avoided: ~$18M (40% of $46M)

VERDICT: More complex, but transfers MORE wealth.
═══════════════════════════════════════════════════════
"

-- Strategy 3: Private Placement Life Insurance (PPLI)
-- Uses: §7702 (life insurance), §72(e) (policy loans)
def ppli : String := "
STRATEGY: PRIVATE PLACEMENT LIFE INSURANCE
═══════════════════════════════════════════════════════
SETUP:
  1. Buy life insurance policy from offshore insurer
  2. Fund with large premium (min ~$1M)
  3. Invest cash value in hedge funds, PE, etc.

HOW IT WORKS:
  - Inside buildup: §7702 - tax-free growth inside policy
  - Policy loans: §72(e) - borrow against CSV tax-free
  - Death benefit: §101 - income tax-free to beneficiaries

COMPOUNDING:
  - Investment gains inside policy = no current tax
  - Can invest in almost anything (hedge funds, PE, etc.)
  - Score: 10/10

ACCESS:
  - Policy loans up to ~90% of cash value
  - Loans are NOT taxable distributions
  - Interest charged but can be low
  - Score: 7/10 (must keep policy in force)

CONTROL:
  - You pick investments (within insurance wrapper)
  - Insurance company technically owns assets
  - Score: 6/10

RISKS:
  - Must pass §7702 tests (not MEC)
  - Insurance costs eat ~1% annually
  - If policy lapses with loans, gain is taxable
  - Offshore = complexity, potential PFIC issues

NUMBERS ($10M premium, 20 years):
  - Cash value: ~$40M (after insurance costs)
  - Borrow capacity: ~$36M
  - Death benefit: ~$40M+ (tax-free)

VERDICT: Works, but expensive and complex. For $10M+ only.
═══════════════════════════════════════════════════════
"

-- Strategy 4: Roth Conversion Ladder
-- Uses: §408A (Roth IRA)
def rothLadder : String := "
STRATEGY: MEGA BACKDOOR ROTH + CONVERSION LADDER
═══════════════════════════════════════════════════════
SETUP (ACCUMULATION):
  1. Max 401k ($23K/yr)
  2. Max Mega Backdoor Roth ($46K/yr after-tax → Roth)
  3. Max Backdoor Roth IRA ($7K/yr)
  Total: ~$76K/yr into Roth

SETUP (CONVERSION):
  1. In low-income years, convert Traditional to Roth
  2. Pay tax at low rates (0-22%)
  3. 5-year clock on conversions

COMPOUNDING:
  - Roth = 100% tax-free forever
  - No RMDs
  - Score: 10/10

ACCESS:
  - Contributions: withdraw anytime
  - Conversions: withdraw after 5 years
  - Earnings: withdraw after 59.5
  - Score: 6/10 (age restrictions)

CONTROL:
  - Self-directed Roth: invest in almost anything
  - Score: 7/10

NUMBERS (20 years @ $76K/yr, 8% return):
  - Total contributions: $1.52M
  - Ending value: ~$4M
  - Tax on withdrawal: $0

VERDICT: Best for W-2 employees. Limited by contribution caps.
═══════════════════════════════════════════════════════
"

#eval buyBorrowDie
#eval idgtInstallment
#eval ppli
#eval rothLadder

/-!
## FINAL RANKING
-/

#eval "
════════════════════════════════════════════════════════════
FINAL RANKING: COMPOUND + ACCESS + CONTROL
════════════════════════════════════════════════════════════

For $10M+ liquid wealth:

1. IDGT + INSTALLMENT SALE + BORROW
   Compound: 10 | Access: 8 | Control: 8 | Total: 720
   Best for: Estate planning + current access

2. BUY-BORROW-DIE
   Compound: 10 | Access: 8 | Control: 10 | Total: 800
   Best for: Simplicity, max control

3. PPLI
   Compound: 10 | Access: 7 | Control: 6 | Total: 420
   Best for: Alternative investments, offshore

For W-2 income (under $1M/yr):

1. MEGA BACKDOOR ROTH
   Compound: 10 | Access: 6 | Control: 7 | Total: 420
   Best for: Long-term, tax-free retirement

════════════════════════════════════════════════════════════
THE ANSWER TO YOUR QUESTION:

'Put wealth where it compounds tax-free, enjoy it, control it'

→ BUY-BORROW-DIE if you want simplicity and control
→ IDGT if you also want estate tax elimination
→ PPLI if you want alternative investments

All three let you:
✓ Compound tax-free (or tax-deferred forever)
✓ Access via borrowing (no tax event)
✓ Maintain meaningful control

The 'loophole' is: BORROWING IS NOT A TAXABLE EVENT.
Combined with STEP-UP AT DEATH, you never pay tax.

This isn't a bug in the tax code - it's how the wealthy
have operated for decades. It's legal, established, and
exactly what family offices do.
════════════════════════════════════════════════════════════
"
