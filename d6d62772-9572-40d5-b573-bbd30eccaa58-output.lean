/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d6d62772-9572-40d5-b573-bbd30eccaa58

The following was proved by Aristotle:

- theorem crt_approach :
    ∃ (primes : ℕ → List ℕ) (combine : List ℕ → ℕ),
      -- For n-bit integers, use O(n/log n) primes of size O(log n)
      (∀ n, n ≥ 2 → (primes n).length ≤ n / (Nat.log2 n + 1) + 1) ∧
      -- Each prime multiplication is O(log² n) via schoolbook
      -- Total: O(n/log n) * O(log² n) = O(n log n)
      True
-/

/-
ALGORITHM DISCOVERY: Integer Multiplication - Remove log* Factor

PROBLEM: Find pure O(n log n) integer multiplication,
removing the 2^O(log* n) factor from current best.

CURRENT STATE:
- Best known: O(n log n · 2^O(log* n)) (Harvey-van der Hoeven, 2019)
- Conjectured optimal: O(n log n)
- Gap: The iterated logarithm factor

WHY IMPROVEMENT IS BELIEVED POSSIBLE:
- FFT gives O(n log n) for polynomial mult over C
- The log* factor comes from carrying overhead
- Harvey-van der Hoeven nearly achieved pure O(n log n)

GOAL: Prove pure O(n log n) integer multiplication exists.

FIXES from v1:
- Added termination_by for logStar
- Fixed section structure
- Simplified to avoid namespace issues
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown constant `Nat.log2_lt_self`-/
set_option maxHeartbeats 400000

open Nat

noncomputable section

/-- Iterated logarithm with explicit termination -/
def logStar : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => if h : n + 2 ≤ 2 then 1 else 1 + logStar (Nat.log2 (n + 2))
termination_by n => n
decreasing_by
  simp_wf
  have h1 : Nat.log2 (n + 2) < n + 2 := Nat.log2_lt_self (by omega)
  omega

/-- Bit complexity of an integer multiplication algorithm -/
structure IntMultAlgorithm where
  bitOps : ℕ → ℕ
  correct : True

-- placeholder

/-- Harvey-van der Hoeven bound: n log n · 2^O(log* n) -/
def hvdhBound (n : ℕ) : ℕ :=
  n * (Nat.log2 n + 1) * (2 ^ (4 * logStar n + 4))

/-- Pure O(n log n) bound -/
def pureNLogN (c n : ℕ) : ℕ :=
  c * n * (Nat.log2 n + 1)

/-- Current best achieves HVDH bound -/
axiom current_best : ∃ alg : IntMultAlgorithm, ∀ n, alg.bitOps n ≤ hvdhBound n

/-! ## The Main Theorems -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Invalid field notation: Type is not of the form `C ...` where C is a constant
  alg
has type
  IntMultAlgorithm
Function expected at
  pureNLogN
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  c-/
/--
THE IMPROVEMENT THEOREM: Pure O(n log n) integer multiplication exists

This would be a major algorithmic breakthrough, removing the log* factor
from Harvey-van der Hoeven 2019.
-/
theorem integer_mult_pure_nlogn :
    ∃ (alg : IntMultAlgorithm) (c : ℕ),
      c > 0 ∧ ∀ n, n ≥ 2 → alg.bitOps n ≤ pureNLogN c n := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  pureNLogN
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  64-/
/--
FFT over suitable ring approach

If we can find a ring where FFT works without the recursive prime-splitting
that causes the log* factor, we get pure O(n log n).
-/
theorem fft_ring_exists :
    ∃ (p : ℕ) (hp : p.Prime) (ω : ZMod p),
      ω ^ (p - 1) = 1 ∧
      ∀ n, ∃ (ops : ℕ), ops ≤ pureNLogN 64 n := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  pureNLogN
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  100-/
/--
Number-theoretic transform without log* overhead

The key insight would be avoiding the recursive splitting in NTT
that currently requires log* levels of recursion.
-/
theorem ntt_removes_logstar :
    ∃ (transform : ℕ → ℕ → ℕ),
      ∀ n, n ≥ 2 → transform n n ≤ pureNLogN 100 n := by
  sorry

/--
Alternative: Direct construction via Chinese Remainder Theorem

Use CRT to combine results from multiple small primes,
avoiding the recursive structure entirely.
-/
theorem crt_approach :
    ∃ (primes : ℕ → List ℕ) (combine : List ℕ → ℕ),
      -- For n-bit integers, use O(n/log n) primes of size O(log n)
      (∀ n, n ≥ 2 → (primes n).length ≤ n / (Nat.log2 n + 1) + 1) ∧
      -- Each prime multiplication is O(log² n) via schoolbook
      -- Total: O(n/log n) * O(log² n) = O(n log n)
      True := by
  -- We can define `primes` as the empty list for all `n`.
  use fun n => []
  simp

end