import Common.Basic

/-!
# IRC Section 65 - Ordinary Loss Defined

For purposes of the Internal Revenue Code, defines "ordinary loss" as including
any loss from the sale or exchange of property which is not a capital asset.

## References
- [26 USC §65](https://www.law.cornell.edu/uscode/text/26/65)

## Key Provisions
- Ordinary loss includes losses from non-capital assets
- Any loss treated as "ordinary loss" under other IRC provisions is also ordinary loss
-/

-- Loss from sale or exchange (negative amount)
structure PropertyLoss where
  amount : Currency  -- Negative value representing loss
  isCapitalAsset : Bool
  deriving Repr

-- Determine if a loss is an ordinary loss
def isOrdinaryLoss (loss : PropertyLoss) : Bool :=
  not loss.isCapitalAsset

-- Calculate total ordinary losses
def calculateOrdinaryLoss (losses : List PropertyLoss) : Currency :=
  losses.foldl (fun (acc : Int) l =>
    let amt : Int := l.amount
    if isOrdinaryLoss l then acc + amt else acc) (0 : Int)

-- Examples
def example_inventory_loss : PropertyLoss :=
  ⟨(-50000 : Int), false⟩  -- -$500 loss from inventory (ordinary property)

def example_stock_loss : PropertyLoss :=
  ⟨(-100000 : Int), true⟩  -- -$1,000 loss from stock (capital asset)

#eval isOrdinaryLoss example_inventory_loss   -- true
#eval isOrdinaryLoss example_stock_loss       -- false
#eval calculateOrdinaryLoss [example_inventory_loss, example_stock_loss]  -- -50000

-- Theorem: Ordinary losses are non-positive
-- Note: Full proof requires custom lemma about fold accumulator monotonicity
theorem ordinary_loss_nonpositive (losses : List PropertyLoss)
    (h : ∀ l ∈ losses, (l.amount : Int) ≤ 0) :
    calculateOrdinaryLoss losses ≤ 0 := by
  sorry

-- Theorem: Capital asset losses don't contribute to ordinary loss
theorem capital_losses_excluded (l : PropertyLoss)
    (h : l.isCapitalAsset = true) :
    isOrdinaryLoss l = false := by
  simp [isOrdinaryLoss, h]

-- Theorem: All non-capital losses are ordinary
theorem noncapital_is_ordinary (l : PropertyLoss)
    (h : l.isCapitalAsset = false) :
    isOrdinaryLoss l = true := by
  simp [isOrdinaryLoss, h]
