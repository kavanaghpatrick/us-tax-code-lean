import Common.Basic

namespace TaxCode.Section1221

/-!
Implementation of IRC Section 1221: Capital Asset Defined.
This module provides a formalization of the definition of a capital asset,
excluding the eight statutory exceptions under §1221(a)(1)-(8).
-/

/-- Inductive type for classifying property types, covering categories relevant to the eight exceptions in IRC §1221(a). -/
inductive PropertyType where
  | StockInTrade
  | Inventory
  | Depreciable
  | Real
  | Creative
  | Receivable
  | GovPublication
  | DerivativeInstrument
  | Hedging
  | Supply
  | Security
  | Other
  deriving BEq, Repr

/-- Structure holding information about a property, including its type and flags for exception checks. -/
structure PropertyInfo where
  tp : PropertyType
  heldPrimarilyForSale : Bool := false
  usedInTradeOrBusiness : Bool := false
  subjectToDepreciation : Bool := false
  heldByCreator : Bool := false
  fromInventoryOrService : Bool := false
  receivedOtherThanPurchase : Bool := false
  isCommodityDerivative : Bool := false
  heldByDealer : Bool := false
  isIdentifiedHedging : Bool := false
  regularlyUsedInBusiness : Bool := false
  deriving Repr

/-- Checks if property falls under exception (a)(1): stock in trade, inventory, or property held primarily for sale to customers in the ordinary course of trade or business.
Reference: IRC §1221(a)(1) -/
def isException1 (p : PropertyInfo) : Bool :=
  match p.tp with
  | .StockInTrade => true
  | .Inventory => true
  | _ => p.heldPrimarilyForSale

/-- Checks if property falls under exception (a)(2): depreciable property used in trade or business, or real property used in trade or business.
Reference: IRC §1221(a)(2) -/
def isException2 (p : PropertyInfo) : Bool :=
  match p.tp with
  | .Depreciable => p.subjectToDepreciation && p.usedInTradeOrBusiness
  | .Real => p.usedInTradeOrBusiness
  | _ => false

/-- Checks if property falls under exception (a)(3): copyrights, literary, musical, or artistic compositions, etc.
Reference: IRC §1221(a)(3) -/
def isException3 (p : PropertyInfo) : Bool :=
  match p.tp with
  | .Creative => p.heldByCreator
  | _ => false

/-- Checks if property falls under exception (a)(4): accounts or notes receivable from sale of inventory or services.
Reference: IRC §1221(a)(4) -/
def isException4 (p : PropertyInfo) : Bool :=
  match p.tp with
  | .Receivable => p.fromInventoryOrService
  | _ => false

/-- Checks if property falls under exception (a)(5): U.S. Government publications received other than by purchase.
Reference: IRC §1221(a)(5) -/
def isException5 (p : PropertyInfo) : Bool :=
  match p.tp with
  | .GovPublication => p.receivedOtherThanPurchase
  | _ => false

/-- Checks if property falls under exception (a)(6): commodities derivative financial instruments held by dealers.
Reference: IRC §1221(a)(6) -/
def isException6 (p : PropertyInfo) : Bool :=
  match p.tp with
  | .DerivativeInstrument => p.isCommodityDerivative && p.heldByDealer
  | _ => false

/-- Checks if property falls under exception (a)(7): certain identified hedging transactions.
Reference: IRC §1221(a)(7) -/
def isException7 (p : PropertyInfo) : Bool :=
  match p.tp with
  | .Hedging => p.isIdentifiedHedging
  | _ => false

/-- Checks if property falls under exception (a)(8): supplies regularly used or consumed in the ordinary course of business.
Reference: IRC §1221(a)(8) -/
def isException8 (p : PropertyInfo) : Bool :=
  match p.tp with
  | .Supply => p.regularlyUsedInBusiness
  | _ => false

/-- Determines if the given property is a capital asset per IRC §1221.
Returns true if the property does not fall under any of the eight exceptions. -/
def isCapitalAsset (p : PropertyInfo) : Bool :=
  !(isException1 p || isException2 p || isException3 p || isException4 p || isException5 p || isException6 p || isException7 p || isException8 p)

/-- Theorem: Inventory is not a capital asset.
Reference: IRC §1221(a)(1) -/
theorem inventory_not_capital (p : PropertyInfo) (h : p.tp = PropertyType.Inventory) : isCapitalAsset p = false := by
  unfold isCapitalAsset
  simp only [isException1, h, isException2, isException3, isException4, isException5, isException6, isException7, isException8]
  simp

/-- Theorem: Securities are capital assets unless held primarily for sale (e.g., dealer inventory exception).
Reference: IRC §1221(a)(1) -/
theorem securities_are_capital_unless_dealer_exception (p : PropertyInfo)
  (h_tp : p.tp = PropertyType.Security) (h_sale : p.heldPrimarilyForSale = false) :
  isCapitalAsset p = true := by
  unfold isCapitalAsset isException1 isException2 isException3 isException4 isException5 isException6 isException7 isException8
  simp [h_tp, h_sale]

/-- Theorem: Real property is generally a capital asset unless used in trade/business or held for sale.
Reference: IRC §1221(a)(2) and §1221(a)(1) -/
theorem real_property_generally_capital (p : PropertyInfo)
  (h_tp : p.tp = PropertyType.Real) (h_business : p.usedInTradeOrBusiness = false)
  (h_sale : p.heldPrimarilyForSale = false) :
  isCapitalAsset p = true := by
  unfold isCapitalAsset isException1 isException2 isException3 isException4 isException5 isException6 isException7 isException8
  simp [h_tp, h_business, h_sale]

/-- Example: Stock held for investment (capital asset). -/
def exampleStock : PropertyInfo := {
  tp := .Security,
  heldPrimarilyForSale := false
}

/-- Example: Inventory (not a capital asset). -/
def exampleInventory : PropertyInfo := {
  tp := .Inventory
}

/-- Example: Real estate held for investment (capital asset). -/
def exampleRealEstateInvestment : PropertyInfo := {
  tp := .Real,
  usedInTradeOrBusiness := false,
  heldPrimarilyForSale := false
}

/-- Example: Real estate used in business (not a capital asset). -/
def exampleRealEstateBusiness : PropertyInfo := {
  tp := .Real,
  usedInTradeOrBusiness := true,
  heldPrimarilyForSale := false
}

end TaxCode.Section1221