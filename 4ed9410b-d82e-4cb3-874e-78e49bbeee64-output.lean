/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4ed9410b-d82e-4cb3-874e-78e49bbeee64
-/

/-
Erdős Problem #730 - Central Binomial Coefficients Sharing Prime Divisors
KUMMER'S THEOREM APPROACH

PROBLEM: Are there infinitely many pairs n < m where C(2n,n) and C(2m,m)
have the same prime factors?

KNOWN EXAMPLES: (87,88), (607,608) - all consecutive!
AlphaProof found: (10003, 10005) - non-consecutive

KEY INSIGHT - KUMMER'S THEOREM:
- v_p(C(2n,n)) = number of carries when adding n + n in base p
- p | C(2n,n) iff there's at least one carry
- Carry occurs iff some digit of n in base p is ≥ ⌈p/2⌉

DIGIT CHARACTERIZATION:
p ∈ primeFactors(C(2n,n)) ↔ n has a digit ≥ ⌈p/2⌉ in base p

WHY (87, 88) WORKS:
- 87 = 1·64 + 0·8 + 7 in base 8, digit 7 ≥ 4 ✓
- 88 = 1·64 + 1·8 + 0 in base 8, digit 1 ≥ 4? No...
- Actually need to check each prime separately
- The recurrence: C(176,88) = C(174,87) * (175·176) / (88²)
- 175 = 5² · 7, 176 = 16 · 11, 88 = 8 · 11
- New factors must already divide C(174,87)
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Ambiguous term
  centralBinom
Possible interpretations:
  _root_.centralBinom n : ℕ
  
  n.centralBinom : ℕ
Ambiguous term
  centralBinom
Possible interpretations:
  _root_.centralBinom m : ℕ
  
  m.centralBinom : ℕ
Unknown identifier `m`
Unknown identifier `m`
Unknown identifier `m`-/
set_option maxHeartbeats 400000

open Nat Finset

/-- Central binomial coefficient C(2n, n) -/
abbrev centralBinom (n : ℕ) : ℕ := n.centralBinom

/-- The set of prime factors -/
abbrev primeSupport (n : ℕ) : Finset ℕ := n.primeFactors

/-- The main relation: same prime factors -/
def SamePrimeFactors (n m : ℕ) : Prop :=
  primeSupport (centralBinom n) = primeSupport (centralBinom m)

/-- The set of valid pairs -/
def centralBinomPairs : Set (ℕ × ℕ) :=
  {(n, m) | n < m ∧ SamePrimeFactors n m}

/-! ## Kummer's Theorem Characterization -/

/-- Whether n has a digit ≥ threshold in base p -/
def hasLargeDigit (n p : ℕ) (threshold : ℕ) : Prop :=
  ∃ k, (n / p ^ k) % p ≥ threshold

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  centralBinom
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  hasLargeDigit
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  n-/
/-- Kummer's theorem: p | C(2n,n) iff adding n+n in base p has a carry.
    This happens iff n has a digit ≥ ⌈p/2⌉ in base p. -/
lemma kummer_centralBinom (n p : ℕ) (hp : p.Prime) (hp2 : p ≥ 2) :
    p ∣ centralBinom n ↔ hasLargeDigit n p ((p + 1) / 2) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  primeSupport
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (centralBinom n)
Function expected at
  hasLargeDigit
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  n-/
/-- Prime factors characterized by digits -/
lemma primeFactors_centralBinom_iff (n p : ℕ) (hp : p.Prime) :
    p ∈ primeSupport (centralBinom n) ↔ hasLargeDigit n p ((p + 1) / 2) := by
  sorry

/-! ## Recurrence Relation -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  centralBinom
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (n + 1)
Function expected at
  centralBinom
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n
`simp` made no progress-/
/-- The recurrence: (n+1) · C(2(n+1), n+1) = 2(2n+1) · C(2n, n) -/
theorem centralBinom_recurrence (n : ℕ) :
    (n + 1) * centralBinom (n + 1) = 2 * (2 * n + 1) * centralBinom n := by
  simp only [Nat.centralBinom]
  -- Uses Nat.choose recurrence
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  SamePrimeFactors
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n
Function expected at
  primeSupport
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  (centralBinom n)
Function expected at
  primeSupport
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  (centralBinom n)-/
/-- For consecutive pairs, factor equality depends on the ratio -/
lemma consecutive_condition (n : ℕ) (hn : n > 0) :
    SamePrimeFactors n (n + 1) ↔
    (∀ p, p.Prime → p ∣ (2 * n + 1) → p ∈ primeSupport (centralBinom n)) ∧
    (∀ p, p.Prime → p ∣ (n + 1) → p ∈ primeSupport (centralBinom n)) := by
  -- The ratio introduces factors of 2(2n+1) and removes factors of (n+1)²
  -- For sets to be equal, new factors must already exist
  sorry

/-! ## Verified Examples -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  Membership (ℕ × ℕ) ?m.1-/
/-- (87, 88) is a valid pair -/
theorem pair_87_88 : (87, 88) ∈ centralBinomPairs := by
  constructor
  · norm_num
  · unfold SamePrimeFactors primeSupport centralBinom
    native_decide

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  Membership (ℕ × ℕ) ?m.1-/
/-- (607, 608) is a valid pair -/
theorem pair_607_608 : (607, 608) ∈ centralBinomPairs := by
  constructor
  · norm_num
  · unfold SamePrimeFactors primeSupport centralBinom
    native_decide

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  Membership (ℕ × ℕ) ?m.1-/
/-- (1, 2) is NOT a valid pair -/
theorem not_pair_1_2 : (1, 2) ∉ centralBinomPairs := by
  unfold centralBinomPairs SamePrimeFactors
  simp only [Set.mem_setOf_eq, not_and]
  intro _
  -- C(2,1) = 2 has factors {2}
  -- C(4,2) = 6 has factors {2, 3}
  native_decide

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  Membership (ℕ × ℕ) ?m.1-/
/-- (3, 4) is NOT a valid pair -/
theorem not_pair_3_4 : (3, 4) ∉ centralBinomPairs := by
  unfold centralBinomPairs SamePrimeFactors
  simp only [Set.mem_setOf_eq, not_and]
  intro _
  native_decide

/-! ## Infinitude Argument -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  primeSupport
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (centralBinom n)-/
/-- All central binomial coefficients for n > 0 are even -/
theorem two_in_factors (n : ℕ) (hn : n > 0) : 2 ∈ primeSupport (centralBinom n) := by
  rw [Nat.mem_primeFactors]
  constructor
  · exact Nat.two_dvd_centralBinom n hn
  · exact Nat.centralBinom_pos n

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `centralBinomPairs.Infinite`-/
/-- MAIN CONJECTURE: Infinitely many pairs exist -/
theorem erdos_730 : centralBinomPairs.Infinite := by
  -- Strategy: Use density arguments or construct infinite family
  -- The consecutive pairs (87,88), (607,608), ... suggest a pattern
  -- CRT-based construction: find n where digit conditions are satisfied
  sorry

/-! ## Structural Analysis -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `centralBinomPairs`-/
/-- Numbers in OEIS A129515: values n where some m > n satisfies the condition -/
def A129515 : Set ℕ := {n | ∃ m, (n, m) ∈ centralBinomPairs}

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  HasSubset ?m.1-/
/-- Known elements of A129515 -/
theorem known_A129515 : {87, 607} ⊆ A129515 := by
  intro n hn
  rcases hn with rfl | rfl
  · exact ⟨88, pair_87_88⟩
  · exact ⟨608, pair_607_608⟩

end