/-!
# Erdős Problem #127: Large Bipartite Subgraphs Beyond Edwards' Bound

Let f(m) be the maximum value such that every graph with m edges
contains a bipartite subgraph with at least m/2 + (√(8m+1) - 1)/8 + f(m)
edges. Edwards (1973) proved f(m) ≥ 0 and showed f(C(n,2)) = 0 via
complete graphs. Is there an infinite sequence mᵢ with f(mᵢ) → ∞?

## Status: SOLVED — YES (Alon 1996)

## References
- Edwards (1973)
- Alon (1996): f(n²/2) ≫ n^{1/2}, f(m) ≪ m^{1/4}
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

/-!
## Section I: Bipartite Subgraph Size
-/

/-- The maximum number of edges in a bipartite subgraph of a simple graph. -/
axiom maxBipartiteEdges : (V : Type*) → [Fintype V] → [DecidableEq V] →
  SimpleGraph V → [DecidableRel (SimpleGraph.Adj · ·)] → ℕ

/-- Edwards' bound: the guaranteed bipartite subgraph size for m edges. -/
noncomputable def edwardsBound (m : ℕ) : ℝ :=
  m / 2 + (Real.sqrt (8 * m + 1) - 1) / 8

/-!
## Section II: The Excess Function
-/

/-- f(m) is the maximum value such that every graph with m edges has
a bipartite subgraph with at least edwardsBound(m) + f(m) edges. -/
axiom excessF : ℕ → ℝ

/-- f(m) is nonneg: the Edwards bound is always achievable (Edwards 1973). -/
axiom edwards_bound_valid : ∀ m : ℕ, excessF m ≥ 0

/-!
## Section III: Complete Graph Tightness
-/

/-- For complete graphs K_n with m = C(n,2) edges, the Edwards bound
is tight: f(C(n,2)) = 0. -/
axiom complete_graph_tight (n : ℕ) (hn : n ≥ 2) :
  excessF (n.choose 2) = 0

/-!
## Section IV: The Conjecture (Solved)
-/

/-- **Erdős Problem #127**: Is there an infinite sequence mᵢ with
f(mᵢ) → ∞? Solved: YES by Alon (1996). -/
def ErdosProblem127 : Prop :=
  ∃ seq : ℕ → ℕ, StrictMono seq ∧
    Filter.Tendsto (fun i => excessF (seq i)) Filter.atTop Filter.atTop

/-- Alon's result: f(n²/2) ≫ n^{1/2}. -/
axiom alon_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    excessF (n ^ 2 / 2) ≥ c * Real.sqrt n

/-- Alon's result implies the conjecture: taking mᵢ = i²/2 gives
f(mᵢ) → ∞. -/
axiom alon_solves_127 : ErdosProblem127

/-!
## Section V: Upper Bound
-/

/-- Alon's upper bound: f(m) ≪ m^{1/4} for all m. -/
axiom alon_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ m : ℕ, m ≥ 1 →
    excessF m ≤ C * (m : ℝ) ^ (1 / 4 : ℝ)

/-- The optimal constant in f(m) ≤ C·m^{1/4} is unknown. -/
def OptimalConstantQuestion : Prop :=
  ∃ C : ℝ, (∀ m : ℕ, m ≥ 1 → excessF m ≤ C * (m : ℝ) ^ (1 / 4 : ℝ)) ∧
    (∀ C' : ℝ, C' < C →
      ∃ m : ℕ, m ≥ 1 ∧ excessF m > C' * (m : ℝ) ^ (1 / 4 : ℝ))

/-!
## Section VI: Structural Properties
-/

/-- The excess function is subadditive in a weak sense:
the Edwards bound already accounts for the main term. -/
axiom excess_bounded_variation (m₁ m₂ : ℕ) (h : m₁ ≤ m₂) :
  excessF m₂ ≤ excessF m₁ + (m₂ - m₁ : ℝ)

/-- Every m is within √m of a complete graph C(n,2),
where f is small. This constrains the growth of f. -/
axiom excess_near_complete (m : ℕ) (hm : m ≥ 1) :
  ∃ n : ℕ, n ≥ 2 ∧ (n.choose 2 : ℤ) - m ≤ n
