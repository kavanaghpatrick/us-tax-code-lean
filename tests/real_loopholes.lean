/-
REAL TAX LOOPHOLES - Economic Arbitrage Calculations

These are actual tax planning strategies with real dollar amounts,
not just code edge cases.
-/

import Mathlib

/-!
## §831 MICRO-CAPTIVE INSURANCE ARBITRAGE

The REAL loophole: Related party pays "premium" (deductible),
captive only pays tax on investment income under 831(b).
Underwriting profit is TAX-FREE.
-/

def premiumPaid : Int := 1500000      -- $1.5M premium
def claimsPaid : Int := 500000         -- $500K claims (often inflated)
def underwritingProfit : Int := premiumPaid - claimsPaid  -- $1M profit

-- Operating company gets deduction at 21%
def deductionBenefit : Int := (premiumPaid * 21) / 100  -- $315K

-- Captive pays NO TAX on underwriting profit under 831(b)
def taxAvoided : Int := (underwritingProfit * 21) / 100  -- $210K

-- Total arbitrage per year
def microCaptiveArbitrage : Int := deductionBenefit + taxAvoided  -- $525K

#eval s!"=== §831 MICRO-CAPTIVE ARBITRAGE ==="
#eval s!"Premium paid (deductible):    ${premiumPaid}"
#eval s!"Claims paid:                  ${claimsPaid}"
#eval s!"Underwriting profit:          ${underwritingProfit}"
#eval s!"Deduction benefit (21%):      ${deductionBenefit}"
#eval s!"Tax avoided on profit:        ${taxAvoided}"
#eval s!">>> TOTAL ANNUAL ARBITRAGE:   ${microCaptiveArbitrage}"
#eval ""

/-!
## §671-679 INTENTIONALLY DEFECTIVE GRANTOR TRUST (IDGT)

The REAL loophole: Assets removed from estate for estate tax,
but grantor pays income tax. Tax payment is NOT a gift.
Effectively transfers wealth tax-free.
-/

def trustAssets : Int := 10000000      -- $10M trust
def annualIncome : Int := 800000       -- 8% return = $800K
def grantorTaxRate : Int := 37         -- Top marginal rate
def estateTaxRate : Int := 40          -- Estate tax rate

-- Grantor pays income tax on trust income
def annualTaxPaid : Int := (annualIncome * grantorTaxRate) / 100  -- $296K

-- This is NOT a gift - wealth transfers to beneficiaries tax-free
-- Over 20 years:
def years : Int := 20
def totalTaxPaid : Int := annualTaxPaid * years  -- $5.92M transferred

-- Estate tax avoided (assets not in estate)
def estateGrowth : Int := annualIncome * years  -- $16M growth
def estateTaxAvoided : Int := ((trustAssets + estateGrowth) * estateTaxRate) / 100

#eval s!"=== §671-679 IDGT WEALTH TRANSFER ==="
#eval s!"Initial trust assets:         ${trustAssets}"
#eval s!"Annual income (8%):           ${annualIncome}"
#eval s!"Annual tax paid by grantor:   ${annualTaxPaid}"
#eval s!">>> 20-YEAR TAX-FREE TRANSFER: ${totalTaxPaid}"
#eval s!"Estate tax avoided:           ${estateTaxAvoided}"
#eval ""

/-!
## SALE TO GRANTOR TRUST - NO GAIN RECOGNITION

The REAL loophole: Sell appreciated assets to your own
grantor trust. Transaction is IGNORED for income tax.
Installment note payments are NOT income.
-/

def assetBasis : Int := 2000000        -- $2M basis
def assetFMV : Int := 10000000         -- $10M FMV
def builtInGain : Int := assetFMV - assetBasis  -- $8M gain

-- Normal sale: 23.8% on $8M = $1.904M tax
def capitalGainsRate : Int := 238  -- 23.8% (20% + 3.8% NIIT)
def normalTax : Int := (builtInGain * capitalGainsRate) / 1000

-- Sale to IDGT: $0 tax (Rev. Rul. 85-13)
def idgtTax : Int := 0

-- Installment note from trust: NOT taxable income
def installmentPayments : Int := assetFMV  -- $10M over time

#eval s!"=== SALE TO GRANTOR TRUST ==="
#eval s!"Asset basis:                  ${assetBasis}"
#eval s!"Asset FMV:                    ${assetFMV}"
#eval s!"Built-in gain:                ${builtInGain}"
#eval s!"Tax if sold normally (23.8%): ${normalTax}"
#eval s!"Tax if sold to IDGT:          ${idgtTax}"
#eval s!">>> TAX SAVED:                 ${normalTax}"
#eval ""

/-!
## §951A GILTI + QBAI OFFSET

The REAL loophole: Put tangible assets (factories, equipment)
in CFC. 10% deemed return on QBAI is excluded from GILTI.
-/

def cfcIncome : Int := 50000000        -- $50M CFC income
def qbai : Int := 200000000            -- $200M tangible assets
def qbaiReturn : Int := qbai / 10      -- 10% = $20M excluded

def giltiWithoutQBAI : Int := cfcIncome
def giltiWithQBAI : Int := cfcIncome - qbaiReturn

-- Tax difference (10.5% GILTI rate after 50% deduction)
def giltiRate : Int := 105  -- 10.5%
def taxWithoutQBAI : Int := (giltiWithoutQBAI * giltiRate) / 1000
def taxWithQBAI : Int := (giltiWithQBAI * giltiRate) / 1000

#eval s!"=== §951A GILTI + QBAI PLANNING ==="
#eval s!"CFC tested income:            ${cfcIncome}"
#eval s!"QBAI (tangible assets):       ${qbai}"
#eval s!"10% QBAI return (excluded):   ${qbaiReturn}"
#eval s!"GILTI without QBAI:           ${giltiWithoutQBAI}"
#eval s!"GILTI with QBAI:              ${giltiWithQBAI}"
#eval s!"Tax without QBAI (10.5%):     ${taxWithoutQBAI}"
#eval s!"Tax with QBAI (10.5%):        ${taxWithQBAI}"
#eval s!">>> TAX SAVED:                 ${taxWithoutQBAI - taxWithQBAI}"
#eval ""

/-!
## §704(c) PARTNERSHIP BASIS SHIFTING

The REAL loophole: Contribute appreciated property,
non-contributing partners get depreciation deductions
on built-in gain (ceiling rule distortion).
-/

def propertyFMV : Int := 10000000       -- $10M FMV at contribution
def propertyBasis : Int := 2000000      -- $2M basis (built-in gain $8M)
def depreciationLife : Int := 10        -- 10-year depreciation

-- Book depreciation (based on FMV)
def annualBookDep : Int := propertyFMV / depreciationLife  -- $1M/year

-- Tax depreciation available (based on basis)
def annualTaxDep : Int := propertyBasis / depreciationLife  -- $200K/year

-- Under traditional method, only $200K tax depreciation available
-- But $1M book depreciation allocated to partners
-- Ceiling rule: $800K "phantom" deduction for non-contributors

def ceilingRuleDistortion : Int := annualBookDep - annualTaxDep

#eval s!"=== §704(c) CEILING RULE DISTORTION ==="
#eval s!"Property FMV at contribution: ${propertyFMV}"
#eval s!"Property basis:               ${propertyBasis}"
#eval s!"Annual book depreciation:     ${annualBookDep}"
#eval s!"Annual tax depreciation:      ${annualTaxDep}"
#eval s!">>> ANNUAL DISTORTION:         ${ceilingRuleDistortion}"
#eval s!"(Non-contributors get excess book deductions)"
#eval ""

/-!
## SUMMARY: Total Annual Tax Savings
-/

#eval s!"=========================================="
#eval s!"TOTAL ANNUAL LOOPHOLE VALUE (examples):"
#eval s!"  Micro-captive arbitrage:    ${microCaptiveArbitrage}"
#eval s!"  IDGT wealth transfer:       ${annualTaxPaid}"
#eval s!"  Sale to trust (one-time):   ${normalTax}"
#eval s!"  GILTI QBAI offset:          ${taxWithoutQBAI - taxWithQBAI}"
#eval s!"=========================================="
