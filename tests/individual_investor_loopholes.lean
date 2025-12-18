/-
INDIVIDUAL INVESTOR TAX LOOPHOLES

Real strategies for taxable brokerage accounts.
These are the loopholes wealth managers actually use.
-/

import Mathlib

/-!
## Tax Rates (2024)
-/

-- Long-term capital gains rates
def ltcgRate0 : Rat := 0           -- Income up to ~$47K single / $94K MFJ
def ltcgRate15 : Rat := 15/100     -- Middle brackets
def ltcgRate20 : Rat := 20/100     -- Income over ~$518K single
def niit : Rat := 38/1000          -- 3.8% Net Investment Income Tax over $200K/$250K
def topLTCGRate : Rat := 238/1000  -- 20% + 3.8% = 23.8%

-- Short-term / ordinary income rates
def topOrdinaryRate : Rat := 37/100

-- Estate tax
def estateTaxRate : Rat := 40/100
def estateExemption2024 : Int := 13610000  -- $13.61M per person

/-!
## §1014 - STEP-UP IN BASIS AT DEATH

THE BIGGEST LOOPHOLE IN THE TAX CODE.
Unrealized gains DISAPPEAR when you die.
-/

structure Asset where
  name : String
  costBasis : Int
  currentFMV : Int
  deriving Repr

def unrealizedGain (a : Asset) : Int := a.currentFMV - a.costBasis

def taxIfSoldToday (a : Asset) : Int :=
  let gain := unrealizedGain a
  if gain > 0 then (gain * 238) / 1000 else 0  -- 23.8% rate

def taxIfHeldUntilDeath (a : Asset) : Int := 0  -- ZERO!

def basisAfterStepUp (a : Asset) : Int := a.currentFMV  -- Stepped up!

-- Example: Warren Buffett's Berkshire stock
def buffettStock : Asset := {
  name := "Berkshire Hathaway"
  costBasis := 1000000        -- $1M original investment
  currentFMV := 100000000     -- $100M current value
}

#eval s!"=== §1014 STEP-UP IN BASIS ==="
#eval s!"Asset: {buffettStock.name}"
#eval s!"Cost basis:        ${buffettStock.costBasis}"
#eval s!"Current FMV:       ${buffettStock.currentFMV}"
#eval s!"Unrealized gain:   ${unrealizedGain buffettStock}"
#eval s!"Tax if sold today: ${taxIfSoldToday buffettStock}"
#eval s!"Tax if held until death: ${taxIfHeldUntilDeath buffettStock}"
#eval s!">>> TAX AVOIDED:    ${taxIfSoldToday buffettStock}"
#eval s!"Heirs' new basis:  ${basisAfterStepUp buffettStock}"
#eval ""

/-!
## TAX-LOSS HARVESTING (Avoiding §1091 Wash Sales)

Sell losers to realize losses, offset gains.
Must avoid buying "substantially identical" securities within 61-day window.
-/

structure TaxLot where
  ticker : String
  shares : Int
  costBasis : Int
  currentValue : Int
  deriving Repr

def lotGainLoss (lot : TaxLot) : Int := lot.currentValue - lot.costBasis

-- Harvest losses, replace with similar (not identical) ETF
def harvestLoss (loser : TaxLot) (winner : TaxLot) : Int :=
  let loss := lotGainLoss loser
  let gain := lotGainLoss winner
  if loss < 0 && gain > 0 then
    -- Loss offsets gain
    let netGain := gain + loss  -- loss is negative
    let taxWithoutHarvest := (gain * 238) / 1000
    let taxWithHarvest := if netGain > 0 then (netGain * 238) / 1000 else 0
    taxWithoutHarvest - taxWithHarvest
  else 0

-- Example: Harvest S&P 500 loss, buy Total Market ETF
def sp500Loser : TaxLot := {
  ticker := "VOO"
  shares := 100
  costBasis := 50000
  currentValue := 40000  -- $10K loss
}

def techWinner : TaxLot := {
  ticker := "QQQ"
  shares := 50
  costBasis := 20000
  currentValue := 45000  -- $25K gain
}

#eval s!"=== TAX-LOSS HARVESTING ==="
#eval s!"Loser: {sp500Loser.ticker}"
#eval s!"  Basis: ${sp500Loser.costBasis}, Value: ${sp500Loser.currentValue}"
#eval s!"  Loss: ${lotGainLoss sp500Loser}"
#eval s!"Winner: {techWinner.ticker}"
#eval s!"  Basis: ${techWinner.costBasis}, Value: ${techWinner.currentValue}"
#eval s!"  Gain: ${lotGainLoss techWinner}"
#eval s!">>> TAX SAVED BY HARVESTING: ${harvestLoss sp500Loser techWinner}"
#eval s!"(Sell VOO at loss, buy VTI same day - NOT substantially identical)"
#eval ""

/-!
## §1202 QSBS - 100% EXCLUSION

Qualified Small Business Stock: if you hold stock in a C-corp
with <$50M assets for 5+ years, exclude up to $10M or 10x basis.
This is how startup founders pay ZERO tax.
-/

structure QSBSHolding where
  companyName : String
  acquisitionCost : Int
  saleProceeds : Int
  yearsHeld : Nat
  isQualifiedSmallBusiness : Bool
  deriving Repr

def qsbsExclusionLimit (holding : QSBSHolding) : Int :=
  -- Greater of $10M or 10x basis
  max 10000000 (holding.acquisitionCost * 10)

def qsbsExclusionPercent (yearsHeld : Nat) : Rat :=
  if yearsHeld >= 5 then 100/100      -- 100% exclusion
  else if yearsHeld >= 4 then 75/100  -- 75%
  else if yearsHeld >= 3 then 50/100  -- 50%
  else 0/100                          -- No exclusion

def qsbsTaxSavings (holding : QSBSHolding) : Int :=
  if !holding.isQualifiedSmallBusiness then 0
  else
    let gain := holding.saleProceeds - holding.acquisitionCost
    let exclusionPct := qsbsExclusionPercent holding.yearsHeld
    let excludedGain := min gain (qsbsExclusionLimit holding)
    let excluded := (excludedGain * exclusionPct.num) / exclusionPct.den
    -- Tax that would have been paid
    (excluded * 238) / 1000

-- Example: Startup founder sells after IPO
def founderStock : QSBSHolding := {
  companyName := "TechStartup Inc."
  acquisitionCost := 100000      -- $100K for founder shares
  saleProceeds := 15000000       -- $15M at exit
  yearsHeld := 6
  isQualifiedSmallBusiness := true
}

#eval s!"=== §1202 QSBS EXCLUSION ==="
#eval s!"Company: {founderStock.companyName}"
#eval s!"Acquisition cost:  ${founderStock.acquisitionCost}"
#eval s!"Sale proceeds:     ${founderStock.saleProceeds}"
#eval s!"Gain:              ${founderStock.saleProceeds - founderStock.acquisitionCost}"
#eval s!"Years held:        {founderStock.yearsHeld}"
#eval s!"Exclusion limit:   ${qsbsExclusionLimit founderStock}"
#eval s!">>> TAX SAVED:      ${qsbsTaxSavings founderStock}"
#eval s!"(Founder pays $0 on first $10M of gain!)"
#eval ""

/-!
## 0% LONG-TERM CAPITAL GAINS BRACKET

If your taxable income is under ~$47K (single) / $94K (MFJ),
you pay 0% on long-term capital gains!
-/

def ltcgTax (gain : Int) (otherIncome : Int) (filingStatus : String) : Int :=
  let threshold := if filingStatus == "MFJ" then 94050 else 47025
  let roomIn0Bracket := max 0 (threshold - otherIncome)
  let gainAt0 := min gain roomIn0Bracket
  let gainAt15 := max 0 (gain - roomIn0Bracket)
  (gainAt15 * 15) / 100

-- Example: Retired couple with $50K income realizes $40K gain
def retiredCoupleGain : Int := 40000
def retiredCoupleIncome : Int := 50000

#eval s!"=== 0% LTCG BRACKET ==="
#eval s!"Retired couple:"
#eval s!"  Other income:     ${retiredCoupleIncome}"
#eval s!"  LTCG realized:    ${retiredCoupleGain}"
#eval s!"  0% bracket room:  ${max 0 (94050 - retiredCoupleIncome)}"
#eval s!"  Tax on gain:      ${ltcgTax retiredCoupleGain retiredCoupleIncome "MFJ"}"
#eval s!">>> Tax if ordinary income: ${(retiredCoupleGain * 22) / 100}"
#eval s!">>> SAVINGS: ${(retiredCoupleGain * 22) / 100 - ltcgTax retiredCoupleGain retiredCoupleIncome "MFJ"}"
#eval ""

/-!
## CHARITABLE DONATION OF APPRECIATED STOCK

Donate stock instead of cash:
1. Deduct full FMV (not basis)
2. Pay NO capital gains tax on appreciation
-/

def charitableDonationSavings (stock : Asset) (marginalRate : Rat) : Int :=
  let gain := unrealizedGain stock
  -- Deduction value
  let deductionValue := (stock.currentFMV * marginalRate.num) / marginalRate.den
  -- Capital gains tax avoided
  let cgTaxAvoided := if gain > 0 then (gain * 238) / 1000 else 0
  deductionValue + cgTaxAvoided

def charityStock : Asset := {
  name := "Apple shares"
  costBasis := 10000       -- $10K basis
  currentFMV := 100000     -- $100K FMV
}

#eval s!"=== CHARITABLE DONATION OF APPRECIATED STOCK ==="
#eval s!"Stock: {charityStock.name}"
#eval s!"Basis:            ${charityStock.costBasis}"
#eval s!"FMV:              ${charityStock.currentFMV}"
#eval s!"Unrealized gain:  ${unrealizedGain charityStock}"
#eval s!""
#eval s!"If donate CASH of $100K:"
#eval s!"  Deduction value (37%): ${(100000 * 37) / 100}"
#eval s!"  Must sell stock first, pay tax: ${taxIfSoldToday charityStock}"
#eval s!"  Net benefit: ${(100000 * 37) / 100 - taxIfSoldToday charityStock}"
#eval s!""
#eval s!"If donate STOCK directly:"
#eval s!"  Deduction value (37%): ${(charityStock.currentFMV * 37) / 100}"
#eval s!"  Capital gains tax:     $0"
#eval s!">>> NET BENEFIT:          ${charitableDonationSavings charityStock (37/100)}"
#eval s!">>> EXTRA SAVINGS:        ${charitableDonationSavings charityStock (37/100) - ((100000 * 37) / 100 - taxIfSoldToday charityStock)}"
#eval ""

/-!
## BORROW AGAINST PORTFOLIO (BUY-BORROW-DIE)

Instead of selling (taxable), borrow against your portfolio.
Interest may be deductible. No capital gains event.
At death, step-up wipes out the gain.
-/

def borrowingVsSelling (portfolio : Int) (amountNeeded : Int) (basisPct : Rat) : Int :=
  -- If you sell: pay capital gains
  let basis := (portfolio * basisPct.num) / basisPct.den
  let gainIfSell := amountNeeded - (amountNeeded * basisPct.num) / basisPct.den
  let taxIfSell := (gainIfSell * 238) / 1000
  -- If you borrow: interest cost (assume 5% margin rate)
  let annualInterest := (amountNeeded * 5) / 100
  -- Net savings first year (ignoring future interest)
  taxIfSell - annualInterest

#eval s!"=== BUY-BORROW-DIE STRATEGY ==="
#eval s!"Portfolio value:   $10,000,000"
#eval s!"Basis (20%):       $2,000,000"
#eval s!"Cash needed:       $1,000,000"
#eval s!""
#eval s!"Option 1: Sell $1M of stock"
#eval s!"  Gain realized:   $800,000 (80% of sale)"
#eval s!"  Tax (23.8%):     ${(800000 * 238) / 1000}"
#eval s!""
#eval s!"Option 2: Borrow $1M against portfolio"
#eval s!"  Interest (5%):   ${(1000000 * 5) / 100}/year"
#eval s!"  Capital gains:   $0"
#eval s!"  At death: loan repaid, gain stepped-up"
#eval s!""
#eval s!">>> FIRST YEAR SAVINGS: ${borrowingVsSelling 10000000 1000000 (20/100)}"
#eval ""

/-!
## SPECIFIC LOT IDENTIFICATION (HIFO)

When selling, specify which lots to sell.
Sell highest-cost lots first (HIFO) to minimize gain.
-/

structure Position where
  lots : List TaxLot
  deriving Repr

def totalShares (p : Position) : Int :=
  p.lots.foldl (fun acc lot => acc + lot.shares) 0

def avgCostBasis (p : Position) : Int :=
  let totalBasis := p.lots.foldl (fun acc lot => acc + lot.costBasis) 0
  let shares := totalShares p
  if shares == 0 then 0 else totalBasis / shares

-- Tax from selling using average cost vs HIFO
def taxDifferenceHIFO (p : Position) (sharesToSell : Int) (currentPrice : Int) : Int :=
  -- Sort lots by cost basis descending (highest first)
  let sortedLots := p.lots  -- In real impl, would sort
  -- This is simplified - just show the concept
  let proceeds := sharesToSell * currentPrice
  let avgBasis := avgCostBasis p * sharesToSell
  let hifoGain := proceeds - avgBasis  -- Simplified
  (hifoGain * 238) / 1000

-- Example position with multiple lots
def myPosition : Position := {
  lots := [
    { ticker := "AAPL", shares := 100, costBasis := 10000, currentValue := 20000 },  -- $100/share basis
    { ticker := "AAPL", shares := 100, costBasis := 15000, currentValue := 20000 },  -- $150/share basis
    { ticker := "AAPL", shares := 100, costBasis := 18000, currentValue := 20000 }   -- $180/share basis
  ]
}

#eval s!"=== SPECIFIC LOT IDENTIFICATION ==="
#eval s!"Position: 300 shares AAPL"
#eval s!"  Lot 1: 100 shares @ $100 basis"
#eval s!"  Lot 2: 100 shares @ $150 basis"
#eval s!"  Lot 3: 100 shares @ $180 basis"
#eval s!"Current price: $200/share"
#eval s!""
#eval s!"Selling 100 shares:"
#eval s!"  FIFO (Lot 1): Gain = $10,000, Tax = ${(10000 * 238) / 1000}"
#eval s!"  HIFO (Lot 3): Gain = $2,000,  Tax = ${(2000 * 238) / 1000}"
#eval s!">>> SAVINGS FROM HIFO: ${(10000 * 238) / 1000 - (2000 * 238) / 1000}"
#eval ""

/-!
## DIRECT INDEXING (Automated Tax-Loss Harvesting)

Instead of buying S&P 500 ETF, buy all 500 stocks individually.
Harvest losses on individual stocks while maintaining market exposure.
Can generate 1-2% annual tax alpha.
-/

def directIndexingAlpha (portfolioValue : Int) (annualAlphaPct : Rat) (years : Int) : Int :=
  let annualSavings := (portfolioValue * annualAlphaPct.num) / annualAlphaPct.den
  annualSavings * years

#eval s!"=== DIRECT INDEXING ==="
#eval s!"Portfolio:         $5,000,000"
#eval s!"Annual tax alpha:  1.5%"
#eval s!">>> ANNUAL SAVINGS: ${(5000000 * 15) / 1000}"
#eval s!">>> 10-YEAR SAVINGS: ${directIndexingAlpha 5000000 (15/1000) 10}"
#eval ""

/-!
## SUMMARY: Annual Savings for $10M Portfolio
-/

#eval s!"=========================================="
#eval s!"INDIVIDUAL INVESTOR LOOPHOLES SUMMARY"
#eval s!"(Assumes $10M portfolio, 20% cost basis)"
#eval s!"=========================================="
#eval s!"Step-up at death:     ${taxIfSoldToday { name := "", costBasis := 2000000, currentFMV := 10000000 }}"
#eval s!"  (One-time, at death)"
#eval s!""
#eval s!"Tax-loss harvesting:  ~$50,000/year"
#eval s!"  (Depends on volatility)"
#eval s!""
#eval s!"0% LTCG bracket:      $0-$14,000/year"
#eval s!"  (If low other income)"
#eval s!""
#eval s!"Charitable stock:     ~$21,400 extra per $100K donated"
#eval s!"  (vs donating cash)"
#eval s!""
#eval s!"Borrow vs sell:       ~$140,000 per $1M accessed"
#eval s!"  (First year, ignoring interest)"
#eval s!""
#eval s!"HIFO lot selection:   ~$1,900 per $100K sold"
#eval s!"  (Vs FIFO)"
#eval s!""
#eval s!"Direct indexing:      ~$150,000/year"
#eval s!"  (On $10M portfolio)"
#eval s!"=========================================="
