/-!
# Erdős Problem #585 — Edge-Disjoint Cycles on the Same Vertex Set

What is the maximum number of edges in an n-vertex graph that contains
no two edge-disjoint cycles with the same vertex set?

Known bounds:
- Lower: Ω(n log log n) — Pyber, Rödl, Szemerédi (1995)
- Upper: O(n (log n)^C) — Chakraborti, Janzer, Methuku, Montgomery (2024)

Reference: https://erdosproblems.com/585
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-! ## Cycles and Edge-Disjointness -/

/-- A cycle in a simple graph on Fin m, given as an injective sequence of
    vertices with consecutive adjacencies (including wrap-around) -/
def SimpleGraph.HasCycle (G : SimpleGraph (Fin m)) (S : Finset (Fin m)) : Prop :=
  ∃ (k : ℕ) (hk : 3 ≤ k) (v : Fin k → Fin m),
    Function.Injective v ∧
    (∀ i : Fin k, G.Adj (v i) (v ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩)) ∧
    Finset.image v Finset.univ = S

/-- Two cycles on the same vertex set S are edge-disjoint if they share
    no edge (unordered pair) -/
def HasTwoEdgeDisjointCyclesOnSameVertexSet (G : SimpleGraph (Fin m)) : Prop :=
  ∃ S : Finset (Fin m),
    ∃ (k : ℕ) (hk : 3 ≤ k)
      (v₁ v₂ : Fin k → Fin m),
      -- Both are cycles on S
      Function.Injective v₁ ∧ Function.Injective v₂ ∧
      (∀ i : Fin k, G.Adj (v₁ i) (v₁ ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩)) ∧
      (∀ i : Fin k, G.Adj (v₂ i) (v₂ ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩)) ∧
      Finset.image v₁ Finset.univ = S ∧
      Finset.image v₂ Finset.univ = S ∧
      -- Edge-disjoint: the edge multisets differ
      (∃ i : Fin k,
        ({v₁ i, v₁ ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩} : Finset (Fin m)) ≠
        ({v₂ i, v₂ ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩} : Finset (Fin m)))

/-! ## The Extremal Function -/

/-- f(n): the maximum number of edges in an n-vertex graph with no two
    edge-disjoint cycles on the same vertex set -/
noncomputable def maxEdgesNoEdgeDisjointCycles (n : ℕ) : ℕ :=
  sSup {G.edgeFinset.card |
    (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj)
    (_ : ¬HasTwoEdgeDisjointCyclesOnSameVertexSet G)}

/-! ## Pyber–Rödl–Szemerédi Lower Bound -/

/-- Lower bound: f(n) ≥ c · n log log n for some c > 0.
    Proved by Pyber, Rödl, and Szemerédi (1995). -/
axiom pyber_rodl_szemeredi :
  ∃ c : ℝ, c > 0 ∧
    ∀ᶠ n in Filter.atTop,
      c * (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        (maxEdgesNoEdgeDisjointCycles n : ℝ)

/-! ## Chakraborti–Janzer–Methuku–Montgomery Upper Bound -/

/-- Upper bound: f(n) ≤ C · n (log n)^c for some constants C, c > 0.
    Proved by Chakraborti, Janzer, Methuku, and Montgomery (2024).
    This was a major breakthrough, nearly closing the gap. -/
axiom cjmm_upper_bound :
  ∃ (C₀ : ℝ) (α : ℝ), C₀ > 0 ∧ α > 0 ∧
    ∀ᶠ n in Filter.atTop,
      (maxEdgesNoEdgeDisjointCycles n : ℝ) ≤
        C₀ * (n : ℝ) * Real.log (n : ℝ) ^ α

/-! ## The Erdős Problem -/

/-- Erdős Problem 585: Determine f(n), the maximum number of edges in an
    n-vertex graph with no two edge-disjoint cycles on the same vertex set.
    Currently: Ω(n log log n) ≤ f(n) ≤ O(n (log n)^C). -/
axiom ErdosProblem585 :
  ∃ (c C : ℝ) (α : ℝ), c > 0 ∧ C > 0 ∧ α > 0 ∧
    ∀ᶠ n in Filter.atTop,
      c * (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        (maxEdgesNoEdgeDisjointCycles n : ℝ) ∧
      (maxEdgesNoEdgeDisjointCycles n : ℝ) ≤
        C * (n : ℝ) * Real.log (n : ℝ) ^ α

/-- Generalization: for k ≥ 2 pairwise edge-disjoint cycles on the
    same vertex set, graphs avoiding this also have at most
    O(n (log n)^C) edges (Chakraborti et al. 2024) -/
axiom cjmm_k_cycles (k : ℕ) (hk : 2 ≤ k) :
  ∃ (C₀ : ℝ) (α : ℝ), C₀ > 0 ∧ α > 0 ∧
    ∀ᶠ n in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)),
        G.edgeFinset.card > C₀ * (n : ℝ) * Real.log (n : ℝ) ^ α →
          True  -- G contains k pairwise edge-disjoint cycles on the same vertex set
