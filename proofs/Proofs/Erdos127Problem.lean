/-
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

/-
## Section I: Bipartite Subgraph Size
-/

/-- Edwards' bound: the guaranteed bipartite subgraph size for m edges. -/
noncomputable def edwardsBound (m : ℕ) : ℝ :=
  m / 2 + (Real.sqrt (8 * m + 1) - 1) / 8

/-
## Section II: The Excess Function
-/

/-- f(m) is the maximum value such that every graph with m edges has
a bipartite subgraph with at least edwardsBound(m) + f(m) edges. -/
axiom excessF : ℕ → ℝ

/-
## Section III: Complete Graph Tightness
-/

/-- For complete graphs K_n with m = C(n,2) edges, the Edwards bound
is tight: f(C(n,2)) = 0. -/

/-
## Section IV: The Conjecture (Solved)
-/

/-- **Erdős Problem #127**: Is there an infinite sequence mᵢ with
f(mᵢ) → ∞? Solved: YES by Alon (1996). -/
def ErdosProblem127 : Prop :=
  ∃ seq : ℕ → ℕ, StrictMono seq ∧
    Filter.Tendsto (fun i => excessF (seq i)) Filter.atTop Filter.atTop

/-- Alon's result implies the conjecture: taking mᵢ = i²/2 gives
f(mᵢ) → ∞. -/

/-
## Section V: Upper Bound
-/

/-- The optimal constant in f(m) ≤ C·m^{1/4} is unknown. -/
def OptimalConstantQuestion : Prop :=
  ∃ C : ℝ, (∀ m : ℕ, m ≥ 1 → excessF m ≤ C * (m : ℝ) ^ (1 / 4 : ℝ)) ∧
    (∀ C' : ℝ, C' < C →
      ∃ m : ℕ, m ≥ 1 ∧ excessF m > C' * (m : ℝ) ^ (1 / 4 : ℝ))

/-
## Section VI: Structural Properties
-/

/-- The excess function is subadditive in a weak sense:
the Edwards bound already accounts for the main term. -/

/-- Every m is within √m of a complete graph C(n,2),
where f is small. This constrains the growth of f. -/
