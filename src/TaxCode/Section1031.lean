import Lean

namespace Common.Basic

abbrev Currency := Int

abbrev TaxYear := Nat

inductive FilingStatus where
  | single
  | marriedFilingJointly
  | marriedFilingSeparately
  | headOfHousehold
  | qualifyingWidower

end Common.Basic

structure Property where
  basis : Common.Basic.Currency
  fmv : Common.Basic.Currency

structure PropertyExchange where
  tax_year : Common.Basic.TaxYear
  filing_status : Common.Basic.FilingStatus
  given : Property
  received : Property
  boot_paid : Common.Basic.Currency
  boot_received : Common.Basic.Currency

def calculateGainRealized (ex : PropertyExchange) : Int :=
  ex.received.fmv + ex.boot_received - ex.given.basis

def calculateGainRecognized (ex : PropertyExchange) : Int :=
  let realized := calculateGainRealized ex
  if realized > 0 then
    min realized ex.boot_received
  else
    0

def calculateNewBasis (ex : PropertyExchange) : Int :=
  ex.given.basis + ex.boot_paid - ex.boot_received + calculateGainRecognized ex