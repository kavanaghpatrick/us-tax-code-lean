/-
Common definitions inlined for Aristotle processing
-/

-- Currency represented in cents (to avoid floating point issues)
def Currency := Int
  deriving Repr, DecidableEq

namespace Currency

def make (dollars : Int) (cents : Nat) : Currency :=
  dollars * 100 + (cents : Int)

def zero : Currency := (0 : Int)

def toDollars (c : Currency) : Int :=
  let ci : Int := c
  ci / 100

instance (n : Nat) : OfNat Currency n := ⟨(n : Int)⟩

instance : LE Currency where
  le a b := @LE.le Int _ a b

instance : LT Currency where
  lt a b := @LT.lt Int _ a b

-- Arithmetic instances for Currency (delegates to Int since Currency := Int)
instance : HAdd Currency Currency Currency where
  hAdd a b := Int.add a b

instance : HAdd Currency Int Currency where
  hAdd a b := Int.add a b

instance : HAdd Int Currency Currency where
  hAdd a b := Int.add a b

instance : HSub Currency Currency Currency where
  hSub a b := Int.sub a b

instance : HSub Currency Int Currency where
  hSub a b := Int.sub a b

instance : HSub Int Currency Currency where
  hSub a b := Int.sub a b

instance : HMul Currency Currency Currency where
  hMul a b := Int.mul a b

instance : HMul Currency Int Currency where
  hMul a b := Int.mul a b

instance : HMul Int Currency Currency where
  hMul a b := Int.mul a b

instance : HDiv Currency Int Currency where
  hDiv a b := Int.tdiv a b

instance : HDiv Currency Currency Currency where
  hDiv a b := Int.tdiv a b

instance : Max Currency where
  max a b := let ai : Int := a; let bi : Int := b; if ai ≤ bi then bi else ai

instance : Min Currency where
  min a b := let ai : Int := a; let bi : Int := b; if ai ≤ bi then ai else bi

instance : Neg Currency where
  neg a := Int.neg a

end Currency

-- Tax Year
structure TaxYear where
  year : Nat
  h_valid : year ≥ 1913

namespace TaxYear

def current : TaxYear := ⟨2024, by decide⟩

instance : DecidableEq TaxYear := fun a b =>
  match a, b with
  | ⟨y1, _⟩, ⟨y2, _⟩ =>
    if h : y1 = y2 then
      isTrue (by cases h; rfl)
    else
      isFalse (by intro eq; cases eq; exact h rfl)

end TaxYear

-- Filing Status (IRC §1(a)-(e) and §2(b))
inductive FilingStatus
  | Single                         -- IRC §1(c)
  | MarriedFilingJointly          -- IRC §1(a)
  | MarriedFilingSeparately       -- IRC §1(d)
  | HeadOfHousehold               -- IRC §1(b)
  | QualifyingWidower             -- IRC §2(b)
  | Estate                         -- IRC §1(e)(1)
  | Trust                          -- IRC §1(e)(2)
  deriving Repr, DecidableEq, Inhabited

structure Taxpayer where
  id : String
  filingStatus : FilingStatus
  taxYear : TaxYear

instance : Repr Taxpayer where
  reprPrec t _ := s!"Taxpayer(id: {t.id}, status: {repr t.filingStatus}, year: {t.taxYear.year})"


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
