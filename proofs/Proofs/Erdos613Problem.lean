/-
  Erdős Problem #613: Graph Decomposition and Size Ramsey Numbers

  Source: https://erdosproblems.com/613
  Status: DISPROVED (Pikhurko, with Lean verification by Tao)

  Statement:
  Let n ≥ 3 and G be a graph with C(2n+1,2) - C(n,2) - 1 edges.
  Must G be the union of a bipartite graph and a graph with max degree < n?

  Context:
  This is about the size Ramsey number r̂(K_{1,n}, F) where F is all odd cycles.
  The conjecture was that r̂(K_{1,n}, F) = C(2n+1,2) - C(n,2).

  Resolution:
  - Faudree: Holds when G has exactly 2n+1 vertices (unpublished)
  - Pikhurko: DISPROVED the general conjecture
  - Bounds: n² + 0.577n^{3/2} < r̂(K_{1,n}, F) < n² + √2·n^{3/2} + n
  - Tao: Formalized counterexample in Lean (n = 5 fails)
-/

import Mathlib

open Finset Function SimpleGraph Nat

namespace Erdos613

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Edge Counts and Binomial Coefficients -/

/-- The critical edge count from the problem -/
def criticalEdgeCount (n : ℕ) : ℕ :=
  (2*n + 1).choose 2 - n.choose 2 - 1

/-- Simplified form: C(2n+1,2) - C(n,2) - 1 = 2n² + n - n(n-1)/2 - 1 -/
theorem critical_edge_count_formula (n : ℕ) (hn : n ≥ 1) :
    criticalEdgeCount n = n * n + n + (n * (n + 1)) / 2 := by
  sorry

/-- For n = 3: critical count = 9 + 3 + 6 - 1 = 17 -/
example : criticalEdgeCount 3 = 17 := by native_decide

/-- For n = 5: critical count = 55 - 10 - 1 = 44 -/
example : criticalEdgeCount 5 = 44 := by native_decide

/-! ## Graph Decomposition -/

/-- A graph is bipartite iff it has no odd cycles -/
def IsBipartite (G : SimpleGraph V) : Prop :=
  G.IsBipartite

/-- The maximum degree of a graph -/
noncomputable def maxDegree (G : SimpleGraph V) : ℕ :=
  Finset.univ.image (fun v => G.degree v) |>.max' (by simp)

/-- A graph has bounded max degree -/
def HasMaxDegreeLT (G : SimpleGraph V) (k : ℕ) : Prop :=
  maxDegree G < k

/-- G decomposes as union of H₁ and H₂ -/
def IsUnionOf (G H₁ H₂ : SimpleGraph V) : Prop :=
  ∀ v w : V, G.Adj v w ↔ H₁.Adj v w ∨ H₂.Adj v w

/-- The conjectured decomposition property -/
def HasDecomposition (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ H₁ H₂ : SimpleGraph V,
    IsUnionOf G H₁ H₂ ∧
    IsBipartite H₁ ∧
    HasMaxDegreeLT H₂ n

/-! ## The Original Conjecture -/

/-- Original Conjecture: Graphs with critical edge count decompose -/
def OriginalConjecture : Prop :=
  ∀ n : ℕ, n ≥ 3 →
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.edgeFinset.card = criticalEdgeCount n →
      HasDecomposition G n

/-! ## The Size Ramsey Number -/

/-- The star graph K_{1,n} (one center with n leaves) -/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) :=
  sorry -- Center vertex 0 adjacent to all others

/-- A graph contains a star K_{1,n} -/
def ContainsStar (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ v : V, n ≤ G.degree v

/-- A graph contains an odd cycle -/
def ContainsOddCycle (G : SimpleGraph V) : Prop :=
  ¬G.IsBipartite

/-- Size Ramsey number: minimum edges such that any 2-coloring
    has monochromatic K_{1,n} or odd cycle -/
noncomputable def sizeRamseyStarOddCycle (n : ℕ) : ℕ :=
  sorry -- The minimum m such that any graph with m edges
        -- either contains K_{1,n} or is non-bipartite

/-- The conjectured value -/
def conjecturedSizeRamsey (n : ℕ) : ℕ :=
  (2*n + 1).choose 2 - n.choose 2

/-! ## Pikhurko's Disproof -/

/-- Pikhurko's lower bound: r̂ > n² + 0.577n^{3/2} -/
axiom pikhurko_lower_bound :
  ∃ c : ℝ, c > 0.5 ∧
    ∀ n : ℕ, n ≥ 3 →
      (sizeRamseyStarOddCycle n : ℝ) > n^2 + c * n^(3/2 : ℝ)

/-- Pikhurko's upper bound: r̂ < n² + √2·n^{3/2} + n -/
axiom pikhurko_upper_bound :
  ∀ n : ℕ, n ≥ 3 →
    (sizeRamseyStarOddCycle n : ℝ) < n^2 + Real.sqrt 2 * n^(3/2 : ℝ) + n

/-- The conjecture is FALSE -/
theorem original_conjecture_false : ¬OriginalConjecture := by
  sorry

/-! ## Counterexample at n = 5 -/

/-- Tao's Lean-verified counterexample at n = 5 -/
axiom tao_counterexample_n5 :
  ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.edgeFinset.card = criticalEdgeCount 5 ∧
    ¬HasDecomposition G 5

/-- The smallest counterexample is n = 5 -/
theorem smallest_counterexample :
    (∀ n < 5, n ≥ 3 →
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        G.edgeFinset.card = criticalEdgeCount n →
        HasDecomposition G n) ∧
    (∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.edgeFinset.card = criticalEdgeCount 5 ∧
      ¬HasDecomposition G 5) := by
  sorry

/-! ## Faudree's Partial Result -/

/-- Faudree (unpublished): Holds when |V| = 2n + 1 -/
axiom faudree_partial :
  ∀ n : ℕ, n ≥ 3 →
    ∀ (G : SimpleGraph (Fin (2*n + 1))),
      G.edgeFinset.card = criticalEdgeCount n →
      HasDecomposition G n

/-- The vertex count matters! -/
theorem vertex_count_matters :
    (∃ n : ℕ, n ≥ 3 ∧
      (∀ G : SimpleGraph (Fin (2*n + 1)),
        G.edgeFinset.card = criticalEdgeCount n →
        HasDecomposition G n) ∧
      (∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        G.edgeFinset.card = criticalEdgeCount n ∧
        ¬HasDecomposition G n)) := by
  use 5
  refine ⟨by norm_num, ?_, tao_counterexample_n5⟩
  exact faudree_partial 5 (by norm_num)

/-! ## Asymptotic Analysis -/

/-- The gap between bounds -/
def boundGap (n : ℕ) : ℝ :=
  (Real.sqrt 2 - 0.577) * n^(3/2 : ℝ) + n

/-- The gap grows as n^{3/2} -/
theorem gap_growth :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ n : ℕ, n ≥ 3 →
        c₁ * n^(3/2 : ℝ) ≤ boundGap n ∧
        boundGap n ≤ c₂ * n^(3/2 : ℝ) := by
  sorry

/-- The conjectured value differs from truth by Θ(n^{3/2}) -/
theorem conjecture_error :
    ∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, n ≥ 5 →
        |(sizeRamseyStarOddCycle n : ℝ) - conjecturedSizeRamsey n| ≥ c * n^(3/2 : ℝ) := by
  sorry

/-! ## Connection to Ramsey Theory -/

/-- Classical Ramsey number R(s,t) -/
noncomputable def ramseyNumber (s t : ℕ) : ℕ :=
  sorry -- Minimum n such that any 2-coloring of K_n has
        -- monochromatic K_s or K_t

/-- Size Ramsey number generalizes classical Ramsey -/
theorem size_ramsey_generalizes :
    ∀ s t : ℕ, s ≥ 2 → t ≥ 2 →
      sizeRamseyStarOddCycle s ≤ (ramseyNumber s t).choose 2 := by
  sorry

/-! ## Special Cases -/

/-- n = 3: critical count = 17, conjecture holds -/
theorem n3_holds :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.edgeFinset.card = 17 →
      HasDecomposition G 3 := by
  sorry

/-- n = 4: critical count = 29, conjecture holds -/
theorem n4_holds :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.edgeFinset.card = 29 →
      HasDecomposition G 4 := by
  sorry

/-! ## Bipartite Component Analysis -/

/-- In a decomposition, the bipartite part can be made maximal -/
theorem maximal_bipartite_decomposition :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (n : ℕ),
      HasDecomposition G n →
      ∃ H₁ H₂ : SimpleGraph V,
        IsUnionOf G H₁ H₂ ∧
        IsBipartite H₁ ∧
        HasMaxDegreeLT H₂ n ∧
        (∀ H₁' : SimpleGraph V, IsBipartite H₁' →
          (∀ v w, H₁.Adj v w → H₁'.Adj v w) → H₁ = H₁') := by
  sorry

/-! ## Main Problem Status -/

/-- Erdős Problem #613: DISPROVED

    Original conjecture: Graphs with C(2n+1,2) - C(n,2) - 1 edges
    decompose into bipartite + bounded degree.

    Status:
    - n = 3, 4: Conjecture HOLDS
    - n = 5: First COUNTEREXAMPLE (Tao, Lean-verified)
    - General: DISPROVED by Pikhurko
    - Faudree: Holds when |V| = 2n + 1

    Bounds on size Ramsey number:
    n² + 0.577n^{3/2} < r̂(K_{1,n}, F) < n² + √2·n^{3/2} + n -/
theorem erdos_613_status :
    ¬OriginalConjecture ∧
    (∀ n ∈ ({3, 4} : Finset ℕ),
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        G.edgeFinset.card = criticalEdgeCount n →
        HasDecomposition G n) ∧
    (∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.edgeFinset.card = criticalEdgeCount 5 ∧
      ¬HasDecomposition G 5) := by
  refine ⟨original_conjecture_false, ?_, tao_counterexample_n5⟩
  intro n hn
  fin_cases hn <;> [exact n3_holds; exact n4_holds]

#check erdos_613_status
#check pikhurko_lower_bound
#check pikhurko_upper_bound
#check tao_counterexample_n5

end Erdos613
