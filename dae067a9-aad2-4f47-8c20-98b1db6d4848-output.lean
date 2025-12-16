/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dae067a9-aad2-4f47-8c20-98b1db6d4848
-/

/-
Erdős Problem #593 - Hypergraphs with Uncountable Chromatic Number
$500 Prize - SIMPLIFIED VERSION

PROBLEM: Characterize finite 3-uniform hypergraphs appearing in EVERY
3-uniform hypergraph with chromatic number > ℵ₀.

ANSWER: H is unavoidable ↔ H has Property B (is 2-colorable)

This is the hypergraph analog of Galvin's theorem for graphs:
"A graph with χ ≥ ℵ₁ contains all finite bipartite graphs."
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  DecidableEq W

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
set_option maxHeartbeats 400000

open Set Function

noncomputable section

/-! ## Definitions -/

/-- A 3-uniform hypergraph -/
structure Hypergraph3 (V : Type*) where
  edges : Set (Finset V)
  uniform : ∀ e ∈ edges, e.card = 3

variable {V W : Type*}

/-- Property B: 2-colorable so no edge is monochromatic -/
def HasPropertyB (H : Hypergraph3 V) : Prop :=
  ∃ c : V → Bool, ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- Proper coloring with countably many colors -/
def IsProperColoring (H : Hypergraph3 V) (c : V → ℕ) : Prop :=
  ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- Chromatic number > ℵ₀ -/
def HasUncountableChromatic (H : Hypergraph3 V) : Prop :=
  ∀ c : V → ℕ, ¬ IsProperColoring H c

/-- Subhypergraph embedding -/
def EmbedsInto (H : Hypergraph3 V) (G : Hypergraph3 W) : Prop :=
  ∃ f : V → W, Injective f ∧ ∀ e ∈ H.edges, e.image f ∈ G.edges

/-- H appears in all hypergraphs with χ > ℵ₀ -/
def IsUnavoidable (H : Hypergraph3 V) : Prop :=
  Finite V ∧ ∀ (W : Type*) (G : Hypergraph3 W), HasUncountableChromatic G → EmbedsInto H G

/-! ## Key Lemmas -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Hypergraph3
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  V
Function expected at
  HasPropertyB
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  H
Function expected at
  IsUnavoidable
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  H
Tactic `constructor` failed: target is not an inductive datatype

V : Sort u_1
x✝² : Sort u_2
Hypergraph3 : x✝²
x✝¹ : Sort u_3
HasPropertyB : x✝¹
x✝ : Sort u_4
IsUnavoidable : x✝
inst✝ : Finite V
H : sorry
hB : sorry
⊢ sorry-/
/-- Direction 1: Property B → Unavoidable (Galvin direction)
    Uses Ramsey theory: high chromatic implies contains all 2-colorable -/
theorem propertyB_implies_unavoidable [Finite V] (H : Hypergraph3 V)
    (hB : HasPropertyB H) : IsUnavoidable H := by
  constructor
  · exact ‹Finite V›
  · intro W G hchi
    -- Ramsey-theoretic argument: G contains K(n,n) which contains H
    sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Hypergraph3
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  V
Function expected at
  HasPropertyB
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  H
Function expected at
  IsUnavoidable
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  H
No goals to be solved-/
/-- Direction 2: ¬Property B → Avoidable
    Construct high-girth hypergraph avoiding H -/
theorem not_propertyB_implies_avoidable [Finite V] (H : Hypergraph3 V)
    (hnotB : ¬ HasPropertyB H) : ¬ IsUnavoidable H := by
  intro ⟨_, hforall⟩
  -- Construct G with χ > ℵ₀ avoiding H
  sorry

/-! ## Main Characterization -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Hypergraph3
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  V
Function expected at
  IsUnavoidable
but this term has type
  ?m.3

Note: Expected a function because this term is being applied to the argument
  H
Function expected at
  HasPropertyB
but this term has type
  ?m.4

Note: Expected a function because this term is being applied to the argument
  H-/
/-- THE ERDŐS #593 CHARACTERIZATION:
    Unavoidable ↔ Property B -/
theorem erdos_593 [Finite V] (H : Hypergraph3 V) :
    IsUnavoidable H ↔ HasPropertyB H := by
  constructor
  · intro h_unavoid
    by_contra h_notB
    exact not_propertyB_implies_avoidable H h_notB h_unavoid
  · exact propertyB_implies_unavoidable H

/-! ## Examples -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  HasPropertyB
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (⟨∅, fun _ h => h.elim⟩ : Hypergraph3 V)-/
/-- Empty hypergraph has Property B -/
theorem empty_has_propertyB : HasPropertyB (⟨∅, fun _ h => h.elim⟩ : Hypergraph3 V) := by
  use fun _ => true
  intro e he
  exact he.elim

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  HasPropertyB
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  (⟨{{ a, b, c }}, by s0rry⟩ : Hypergraph3 V)-/
/-- Single edge has Property B -/
theorem single_edge_has_propertyB (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    HasPropertyB (⟨{{a, b, c}}, by simp [Finset.card_insert_of_not_mem]; exact ⟨hab, hac, hbc⟩⟩ : Hypergraph3 V) := by
  use fun v => v = a
  intro e he
  simp at he
  use a, by simp [he]
  use b, by simp [he]
  simp [hab]

end