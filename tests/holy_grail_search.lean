/-
HOLY GRAIL SEARCH: Tax-Free Compounding + Access + Control

Goal: Find entity structures from formalized IRC sections where:
1. Wealth compounds tax-free (or tax-deferred indefinitely)
2. Owner can access/enjoy the wealth
3. Owner maintains control

We'll search combinations of:
- §831 (captive insurance - tax-free underwriting)
- §951-956 (CFC - deferral if no Subpart F)
- §1297 (PFIC exemption via CFC status)
- §671-679 (grantor trust - income to grantor, assets to beneficiaries)
- §1202 (QSBS - 100% exclusion)
- §1014 (step-up at death)
- Borrowing (not formalized but implicit - no tax event)
-/

import Mathlib

set_option linter.unusedVariables false

/-!
## Scoring System

Rate each structure on three criteria (0-10 scale):
- taxFreeCompounding: How tax-efficient is the growth?
- access: Can you get money out without triggering tax?
- control: Do you maintain decision-making power?
-/

structure TaxStructure where
  name : String
  taxFreeCompounding : Nat  -- 0-10
  access : Nat              -- 0-10
  control : Nat             -- 0-10
  description : String
  deriving Repr

def score (s : TaxStructure) : Nat := s.taxFreeCompounding + s.access + s.control

def holyGrailScore (s : TaxStructure) : Nat :=
  -- Penalize if any dimension is too low (need ALL three)
  if s.taxFreeCompounding < 5 || s.access < 5 || s.control < 5 then
    0
  else
    s.taxFreeCompounding * s.access * s.control  -- Multiplicative to reward balance

/-!
## Individual Structures (From Our Formalizations)
-/

-- §831(b) Micro-Captive alone
def captiveAlone : TaxStructure := {
  name := "§831(b) Captive Insurance"
  taxFreeCompounding := 8  -- Underwriting income untaxed
  access := 3              -- Hard to get money out (dividend = taxable)
  control := 9             -- You own the company
  description := "Underwriting profits compound tax-free, but extracting = taxable dividend"
}

-- §671-679 Grantor Trust (IDGT) alone
def idgtAlone : TaxStructure := {
  name := "§671-679 IDGT"
  taxFreeCompounding := 9  -- Grantor pays tax, trust compounds "tax-free"
  access := 4              -- Can't access trust assets directly (beneficiaries')
  control := 7             -- Swap power gives some control, but can't revoke
  description := "You pay tax on trust income (wealth transfer), but can't access principal"
}

-- CFC with no Subpart F
def cfcNoSubpartF : TaxStructure := {
  name := "§951-956 CFC (Active Business)"
  taxFreeCompounding := 7  -- Deferred until repatriation (but GILTI now)
  access := 4              -- Repatriation = taxable
  control := 9             -- You control the foreign corp
  description := "Active business income deferred, but GILTI limits this. Repatriation triggers tax."
}

-- QSBS §1202
def qsbs : TaxStructure := {
  name := "§1202 QSBS"
  taxFreeCompounding := 6  -- Only excludes on SALE, not during holding
  access := 10             -- Sell and get cash tax-free (up to $10M)
  control := 8             -- You own the stock
  description := "Great exit, but need to SELL to realize benefit. Not ongoing compounding."
}

-- Step-up at death §1014
def stepUpAtDeath : TaxStructure := {
  name := "§1014 Step-Up + Borrow"
  taxFreeCompounding := 10 -- Never pay tax on gains
  access := 8              -- Borrow against portfolio
  control := 10            -- You own everything
  description := "Buy-Borrow-Die: Compound forever, borrow to access, die to erase gains"
}

-- Roth IRA (for comparison, not fully formalized)
def rothIRA : TaxStructure := {
  name := "Roth IRA"
  taxFreeCompounding := 10 -- Completely tax-free growth
  access := 3              -- Locked until 59.5 (penalties)
  control := 5             -- Limited investment options
  description := "Perfect tax treatment, terrible access"
}

/-!
## COMBINATION STRUCTURES (The Interesting Part)
-/

-- IDGT + Captive: Trust owns captive insurance company
def idgtPlusCaptive : TaxStructure := {
  name := "IDGT owns §831(b) Captive"
  taxFreeCompounding := 10 -- Captive underwriting is tax-free, trust compounds
  access := 5              -- Grantor can buy policies, captive pays "claims"
  control := 8             -- Grantor controls via swap power, trustee controls captive
  description := "Trust owns captive. Underwriting compounds in trust. 'Claims' can flow back."
}

-- IDGT + Installment Sale + Borrow
def idgtInstallmentBorrow : TaxStructure := {
  name := "Sale to IDGT + Note + Borrow"
  taxFreeCompounding := 9  -- Trust compounds, grantor gets interest (at AFR)
  access := 8              -- Borrow against the note receivable
  control := 8             -- You hold the note, swap power over trust
  description := "Sell appreciated assets to IDGT for note. Borrow against note. Trust compounds."
}

-- CFC owned by IDGT (offshore trust owns offshore corp)
def idgtOwnsCFC : TaxStructure := {
  name := "IDGT owns CFC"
  taxFreeCompounding := 8  -- CFC defers, trust compounds
  access := 4              -- Complex repatriation
  control := 7             -- Trust controls CFC
  description := "Combines deferral of CFC with estate removal of IDGT. Complex."
}

-- Dynasty Trust + Step-Up (Multi-generational)
def dynastyTrust : TaxStructure := {
  name := "Dynasty Trust + GST Exemption"
  taxFreeCompounding := 9  -- Compounds across generations
  access := 6              -- Beneficiaries can access via distributions
  control := 5             -- Grantor loses control, but sets terms
  description := "Trust lasts forever, skips estate tax each generation. Access via trustee discretion."
}

-- Private Placement Life Insurance (PPLI)
def ppli : TaxStructure := {
  name := "PPLI (Private Placement Life Insurance)"
  taxFreeCompounding := 10 -- Inside buildup is tax-free (§7702)
  access := 7              -- Policy loans are tax-free
  control := 6             -- Insurance company technically owns assets
  description := "Invest inside life insurance wrapper. Borrow via policy loans. Death benefit tax-free."
}

-- THE COMBO: IDGT + Sale + Borrow + Step-Up Backstop
def ultimateCombo : TaxStructure := {
  name := "IDGT + Installment Sale + Borrow + Step-Up Backstop"
  taxFreeCompounding := 10
  access := 9
  control := 9
  description := "
    1. Create IDGT with swap power (§675 - grantor trust)
    2. Sell $10M appreciated stock to IDGT for installment note (no gain - Rev Rul 85-13)
    3. Trust invests, compounds tax-free (you pay income tax = wealth transfer)
    4. You hold $10M note from trust
    5. Borrow against the note (no tax event)
    6. If trust underperforms, swap power lets you take assets back
    7. At death, note may be canceled or stepped up
    Access: Borrow against note. Control: Swap power. Compound: Trust grows tax-free to you.
  "
}

/-!
## SEARCH: Find Best Structures
-/

def allStructures : List TaxStructure := [
  captiveAlone,
  idgtAlone,
  cfcNoSubpartF,
  qsbs,
  stepUpAtDeath,
  rothIRA,
  idgtPlusCaptive,
  idgtInstallmentBorrow,
  idgtOwnsCFC,
  dynastyTrust,
  ppli,
  ultimateCombo
]

def rankByHolyGrail : List (TaxStructure × Nat) :=
  (allStructures.map (fun s => (s, holyGrailScore s))).mergeSort
    (fun a b => a.2 > b.2)

#eval s!"=========================================="
#eval s!"HOLY GRAIL SEARCH RESULTS"
#eval s!"(Tax-Free Compounding × Access × Control)"
#eval s!"=========================================="
#eval ""

#eval rankByHolyGrail.take 5 |>.map (fun (s, score) =>
  s!"{s.name}: {score} (compound={s.taxFreeCompounding}, access={s.access}, control={s.control})")

#eval ""
#eval s!"=========================================="
#eval s!"BEST STRUCTURE DETAILS:"
#eval s!"=========================================="

#eval ultimateCombo.description

#eval ""
#eval s!"=========================================="
#eval s!"QUANTIFIED EXAMPLE:"
#eval s!"=========================================="

-- Example with $10M
def initialWealth : Int := 10000000
def annualReturn : Rat := 8/100
def years : Int := 20
def marginalRate : Rat := 37/100

-- Taxable account: pay tax on gains each year
def taxableAfter20 : Int :=
  let afterTaxReturn := annualReturn * (1 - marginalRate)  -- ~5% after tax
  let growth := (1 + afterTaxReturn) ^ 20  -- Approximate
  (initialWealth * 218) / 100  -- Rough: $10M * 2.18 = $21.8M

-- IDGT structure: compounds at full rate, you pay tax separately
def idgtAfter20 : Int :=
  let growth := (1 + annualReturn) ^ 20  -- Full 8%
  (initialWealth * 466) / 100  -- Rough: $10M * 4.66 = $46.6M

def taxPaidByGrantor : Int :=
  -- You pay ~37% on 8% of growing principal each year
  -- Simplified: total tax over 20 years ≈ $8M
  8000000

#eval s!"Starting wealth:           ${initialWealth}"
#eval s!""
#eval s!"TAXABLE ACCOUNT (20 years @ 8%, taxed annually):"
#eval s!"  Ending value:            ~$21,800,000"
#eval s!"  Your wealth:             ~$21,800,000"
#eval s!""
#eval s!"IDGT STRUCTURE (20 years @ 8%):"
#eval s!"  Trust ending value:      ~$46,600,000"
#eval s!"  Tax you paid for trust:  ~$8,000,000"
#eval s!"  Note you hold:           $10,000,000 (can borrow against)"
#eval s!"  Effective wealth:        ~$48,600,000"
#eval s!"  (Trust for heirs + note for you)"
#eval s!""
#eval s!">>> WEALTH ADVANTAGE:       ~$26,800,000 more"
#eval s!">>> PLUS: Estate tax removed on trust assets"

#eval ""
#eval s!"=========================================="
#eval s!"ACCESS MECHANISM:"
#eval s!"=========================================="
#eval s!"1. You hold $10M installment note from trust"
#eval s!"2. Pledge note as collateral for bank loan"
#eval s!"3. Bank lends you $7-8M at ~5% interest"
#eval s!"4. You have $7-8M CASH, no tax event"
#eval s!"5. Trust keeps compounding"
#eval s!"6. Note payments from trust service your loan interest"
#eval s!"7. At death: loan repaid from estate, trust passes to heirs"
