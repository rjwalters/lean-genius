/-
  Aristotle targets for Erdős Problem #613: Graph Decomposition and Size Ramsey Numbers
  Routine supporting lemmas for automated proof search.
  See Erdos613Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT theorems about sizeRamseyStarOddCycle (def-sorry in main file)
  - NOT theorems about ramseyNumber (def-sorry in main file)
  - NOT the main disproof (depends on axiomatized Tao counterexample)
  - Routine: decomposition algebra, IsUnionOf symmetry/subgraph facts,
    arithmetic on criticalEdgeCount, and real bounds on boundGap
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos613Aristotle

open Finset SimpleGraph Nat Real

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The critical edge count C(2n+1,2) - C(n,2) - 1 -/
def criticalEdgeCount (n : ℕ) : ℕ :=
  (2 * n + 1).choose 2 - n.choose 2 - 1

/-- G decomposes as union of H₁ and H₂ -/
def IsUnionOf (G H₁ H₂ : SimpleGraph V) : Prop :=
  ∀ v w : V, G.Adj v w ↔ H₁.Adj v w ∨ H₂.Adj v w

/-- A graph decomposes into a bipartite part and a degree-bounded part -/
def HasDecomposition (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ H₁ H₂ : SimpleGraph V,
    IsUnionOf G H₁ H₂ ∧
    H₁.IsBipartite ∧
    ∀ v : V, H₂.degree v < n

/-- The gap between Pikhurko's lower and upper bounds -/
noncomputable def boundGap (n : ℕ) : ℝ :=
  (Real.sqrt 2 - 0.577) * (n : ℝ) ^ (3 / 2 : ℝ) + (n : ℝ)

-- Routine: IsUnionOf is commutative — swap H₁ and H₂.
-- Since ∨ is commutative, ↔ H₁.Adj ∨ H₂.Adj is equivalent to ↔ H₂.Adj ∨ H₁.Adj.
theorem is_union_of_comm (G H₁ H₂ : SimpleGraph V) (h : IsUnionOf G H₁ H₂) :
    IsUnionOf G H₂ H₁ := by
  sorry

-- Routine: The left component is a subgraph when G = H₁ ∪ H₂.
-- H₁.Adj v w → G.Adj v w via Or.inl and the biconditional.
theorem union_le_left (G H₁ H₂ : SimpleGraph V) (h : IsUnionOf G H₁ H₂) :
    H₁ ≤ G := by
  sorry

-- Routine: The right component is a subgraph when G = H₁ ∪ H₂.
-- H₂.Adj v w → G.Adj v w via Or.inr and the biconditional.
theorem union_le_right (G H₁ H₂ : SimpleGraph V) (h : IsUnionOf G H₁ H₂) :
    H₂ ≤ G := by
  sorry

-- Routine: The bottom graph has degree 0 everywhere.
-- ⊥ has no edges so every vertex has degree 0.
theorem bot_degree_zero (v : V) : (⊥ : SimpleGraph V).degree v = 0 := by
  sorry

-- Routine: A bipartite graph trivially decomposes (H₁ = G, H₂ = ⊥).
-- If G itself is bipartite, decompose with an empty bounded-degree component.
-- Since degree in ⊥ is 0 < n for any n ≥ 1, this works.
theorem bipartite_has_decomposition (G : SimpleGraph V) (n : ℕ) (hn : n ≥ 1)
    (hb : G.IsBipartite) : HasDecomposition G n := by
  sorry

-- Routine: criticalEdgeCount is positive for n ≥ 2.
-- For n = 2: C(5,2) - C(2,2) - 1 = 10 - 1 - 1 = 8 > 0.
-- The sequence is strictly increasing, so positivity holds for all n ≥ 2.
theorem criticalEdgeCount_pos (n : ℕ) (hn : n ≥ 2) : 0 < criticalEdgeCount n := by
  sorry

-- Routine: boundGap n is positive for n ≥ 1.
-- (√2 - 0.577) > 0 and n^(3/2) ≥ 1 > 0, so the first term is positive,
-- and we add a positive n term.
theorem boundGap_pos (n : ℕ) (hn : n ≥ 1) : 0 < boundGap n := by
  sorry

-- Routine: boundGap grows as Θ(n^{3/2}).
-- Lower bound: take c₁ = √2 - 0.577 > 0; then c₁ * n^(3/2) ≤ boundGap n trivially.
-- Upper bound: take c₂ = √2 + 1 > 0; for n ≥ 1, n ≤ n^(3/2) gives the bound.
theorem gap_growth :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ n : ℕ, n ≥ 3 →
        c₁ * (n : ℝ) ^ (3 / 2 : ℝ) ≤ boundGap n ∧
        boundGap n ≤ c₂ * (n : ℝ) ^ (3 / 2 : ℝ) := by
  sorry

end Erdos613Aristotle
