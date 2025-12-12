/-
Common Currency type for IRC tax code formalization.
This module defines Currency as Nat (natural numbers) to ensure tax amounts cannot be negative.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

-- Currency as natural numbers (non-negative)
abbrev Currency := Nat

namespace Currency

-- Safe subtraction (returns 0 if would be negative)
def sub (a b : Currency) : Currency :=
  if a ≥ b then a - b else 0

-- Conversion helpers
def ofInt (n : Int) : Currency :=
  if n ≥ 0 then n.toNat else 0

end Currency
