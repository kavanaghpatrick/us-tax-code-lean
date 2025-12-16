/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7336db1f-b88a-4734-8f7c-188879cc78fe
-/

/-
ALGORITHM DISCOVERY: All-Pairs Shortest Paths - Truly Subcubic

PROBLEM: Find truly subcubic APSP: O(n^{3-ε}) for constant ε > 0.

CURRENT STATE:
- Best known: O(n³ / 2^Ω(√log n)) - NOT truly subcubic
- Floyd-Warshall baseline: O(n³)
- Goal: O(n^{3-ε}) for some ε > 0

WHY IMPROVEMENT IS BELIEVED POSSIBLE:
- No strong lower bounds prevent O(n^2.5)
- APSP reduces to (min,+) matrix multiplication
- Near-misses: O(n^2.5) for sparse graphs
- Williams' result shows some improvement is possible

GOAL: Prove truly subcubic APSP exists.

FIXES from v1:
- Use `import Mathlib` instead of specific imports
- Cleaner structure
- Better formalization of bounds
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry800941', 'current_not_truly_subcubic', 'floyd_warshall_exists']-/
set_option maxHeartbeats 400000

open Nat Real

noncomputable section

/-- APSP algorithm abstraction -/
structure APSPAlgorithm where
  /-- Number of operations as function of n vertices -/
  operations : ℕ → ℕ
  /-- Correctness placeholder -/
  correct : True

/-- Floyd-Warshall: O(n³) baseline -/
def floydWarshallOps (n : ℕ) : ℕ := n ^ 3

/-- Williams-style bound: n³ / 2^(c√log n) for some c > 0 -/
noncomputable def subpolynomialImprovement (n : ℕ) : ℝ :=
  if n ≤ 1 then 1
  else (n : ℝ) ^ 3 / (2 : ℝ) ^ Real.sqrt (Real.log n)

/-- Truly subcubic means O(n^{3-ε}) for constant ε > 0 -/
def IsTrulySubcubic (ε : ℝ) (alg : APSPAlgorithm) : Prop :=
  ε > 0 ∧ ∃ c : ℕ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (alg.operations n : ℝ) ≤ c * (n : ℝ) ^ (3 - ε)

/-- Floyd-Warshall achieves O(n³) -/
axiom floyd_warshall_exists : ∃ alg : APSPAlgorithm,
  ∀ n, alg.operations n ≤ floydWarshallOps n

/-- Current best is NOT truly subcubic (only polylog improvement) -/
axiom current_not_truly_subcubic :
  ∀ alg : APSPAlgorithm,
  (∀ n, n ≥ 2 → (alg.operations n : ℝ) ≤ subpolynomialImprovement n) →
  ¬∃ ε > 0, IsTrulySubcubic ε alg

/-! ## The Main Theorems -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  IsTrulySubcubic
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  ε-/
/--
THE IMPROVEMENT THEOREM: Truly subcubic APSP exists

This is a major open problem in fine-grained complexity.
Proving it would have huge implications.
-/
theorem apsp_truly_subcubic_exists :
    ∃ (ε : ℝ) (alg : APSPAlgorithm),
      ε > 0 ∧ IsTrulySubcubic ε alg := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Invalid field notation: Type is not of the form `C ...` where C is a constant
  alg
has type
  APSPAlgorithm-/
/--
(min,+) matrix multiplication approach:
APSP on n vertices reduces to n iterations of (min,+) matrix mult.
If (min,+) MM is O(n^α) for α < 3, then APSP is O(n^{α+1-ε}) or better.
-/
theorem minplus_implies_apsp :
    ∃ (α : ℝ), α < 3 ∧
    -- (min,+) matrix mult in O(n^α)
    (∃ (minplusOps : ℕ → ℕ), ∀ n, n ≥ 2 → (minplusOps n : ℝ) ≤ (n : ℝ) ^ α) →
    -- implies APSP improvement
    ∃ alg : APSPAlgorithm, ∀ n, n ≥ 2 →
      (alg.operations n : ℝ) ≤ (n : ℝ) ^ (α + 0.001) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  IsTrulySubcubic
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  (ε / 2)-/
/--
Reduction to Boolean matrix multiplication:
For unweighted graphs, APSP reduces to BMM.
If BMM is truly subcubic, so is unweighted APSP.
-/
theorem bmm_reduction :
    ∃ (bmmOps : ℕ → ℕ) (ε : ℝ),
      ε > 0 ∧
      (∀ n, n ≥ 2 → (bmmOps n : ℝ) ≤ (n : ℝ) ^ (3 - ε)) →
      ∃ alg : APSPAlgorithm, IsTrulySubcubic (ε / 2) alg := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  OfScientific ℕ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Function expected at
  IsTrulySubcubic
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  0.4-/
/--
Algebraic approach: If standard matrix multiplication has ω < 3,
and we can "lift" this to (min,+) semiring, we get subcubic APSP.
Current ω ≈ 2.37, but (min,+) lacks additive inverses.
-/
theorem algebraic_lift :
    -- If ω < 2.5 (hypothetically)
    (∀ n : ℕ, n ≥ 2 → ∃ (ops : ℕ), ops ≤ n ^ 3 ∧ (ops : ℝ) ≤ (n : ℝ) ^ 2.5) →
    -- And we can lift to (min,+) with small overhead
    (∃ (overhead : ℕ → ℕ), ∀ n, overhead n ≤ n * Nat.log2 n) →
    -- Then APSP is subcubic
    ∃ alg : APSPAlgorithm, IsTrulySubcubic 0.4 alg := by
  sorry

end