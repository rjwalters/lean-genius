/-!
# Erdős Problem #1013: Triangle-Free Chromatic Threshold

Let h₃(k) be the smallest n such that there exists a triangle-free graph
on n vertices with chromatic number k. Find an asymptotic formula for h₃(k).
Is it true that h₃(k+1)/h₃(k) → 1?

## Key Results

- **Lower bound**: h₃(k) ≥ (1/2 − o(1))·k²·log k
- **Upper bound**: h₃(k) ≤ (1 + o(1))·k²·log k
- **Graver–Yackel** (1968): h₃(k) ≫ (log k / log log k)·k²
- **Open**: exact asymptotic constant and ratio convergence

## References

- Graver, Yackel (1968)
- Related: Problem #1104 (dual function f(n)), Problem #920 (K_r-free)
- OEIS A292528
- <https://erdosproblems.com/1013>
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- A graph is triangle-free if it contains no clique of size 3. -/
def IsTriangleFree (G : SimpleGraph (Fin n)) : Prop :=
  ¬∃ (a b c : Fin n), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- A proper k-coloring of graph G: assignment of colors 1..k to vertices
    such that adjacent vertices get different colors. -/
def HasProperColoring (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ f : Fin n → Fin k, ∀ (u v : Fin n), G.Adj u v → f u ≠ f v

/-- The chromatic number of G: the minimum k for which a proper k-coloring exists. -/
noncomputable def chromaticNumber (G : SimpleGraph (Fin n)) : ℕ :=
  sSup {k : ℕ | ¬HasProperColoring G k} + 1

/-- h₃(k): the smallest n such that there exists a triangle-free graph
    on n vertices with chromatic number ≥ k. -/
noncomputable def triangleFreeChromThreshold (k : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    n < m → IsTriangleFree G → HasProperColoring G k}

/-! ## Main Conjecture -/

/-- **Erdős's Conjecture (Asymptotic)**: h₃(k) ~ c·k²·log k for some
    constant c. Combined with known bounds, c ∈ [1/2, 1]. -/
axiom erdos_1013_asymptotic :
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto
      (fun k => (triangleFreeChromThreshold k : ℝ) / ((k : ℝ) ^ 2 * Real.log k))
      Filter.atTop (nhds c)

/-- **Ratio Convergence**: h₃(k+1)/h₃(k) → 1 as k → ∞.
    The threshold grows smoothly without large jumps. -/
axiom erdos_1013_ratio_convergence :
  Filter.Tendsto
    (fun k => (triangleFreeChromThreshold (k + 1) : ℝ) /
              (triangleFreeChromThreshold k : ℝ))
    Filter.atTop (nhds 1)

/-! ## Known Bounds -/

/-- **Lower bound**: h₃(k) ≥ (1/2 − o(1))·k²·log k.
    No triangle-free graph on fewer vertices can have chromatic number k. -/
axiom lower_bound :
  ∀ ε : ℝ, ε > 0 → ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
    (triangleFreeChromThreshold k : ℝ) ≥ (1/2 - ε) * (k : ℝ) ^ 2 * Real.log k

/-- **Upper bound**: h₃(k) ≤ (1 + o(1))·k²·log k.
    There exist triangle-free graphs achieving chromatic number k
    on this many vertices. -/
axiom upper_bound :
  ∀ ε : ℝ, ε > 0 → ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
    (triangleFreeChromThreshold k : ℝ) ≤ (1 + ε) * (k : ℝ) ^ 2 * Real.log k

/-- **Graver–Yackel** (1968): h₃(k) ≫ (log k / log log k)·k².
    Early lower bound using probabilistic deletion. -/
axiom graver_yackel_bound :
  ∃ c : ℝ, c > 0 → ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
    (triangleFreeChromThreshold k : ℝ) ≥
      c * (k : ℝ) ^ 2 * Real.log k / Real.log (Real.log k)

/-! ## Structural Properties -/

/-- Monotonicity: h₃ is non-decreasing. Higher chromatic number needs more vertices. -/
axiom threshold_mono :
  ∀ j k : ℕ, j ≤ k → triangleFreeChromThreshold j ≤ triangleFreeChromThreshold k

/-- h₃(1) = 1: a single vertex has chromatic number 1 and is trivially triangle-free. -/
axiom threshold_one :
  triangleFreeChromThreshold 1 = 1

/-- h₃(2) = 1: any non-empty graph has chromatic number ≥ 2,
    so a single vertex (χ = 1) suffices to block χ ≥ 2 on 1 vertex.
    Actually h₃(2) = 2: need an edge (K₂) for χ = 2. -/
axiom threshold_two :
  triangleFreeChromThreshold 2 = 2

/-- h₃(3) = 5: the Mycielski graph M₃ (cycle C₅) has 5 vertices, is triangle-free,
    and has chromatic number 3. -/
axiom threshold_three :
  triangleFreeChromThreshold 3 = 5

/-- h₃(4) = 11: the Mycielski graph M₄ (Grötzsch graph) has 11 vertices,
    is triangle-free, with chromatic number 4. -/
axiom threshold_four :
  triangleFreeChromThreshold 4 = 11

/-- Mycielski's construction: for each k ≥ 2, there exists a triangle-free
    graph with chromatic number k. This proves h₃(k) is finite. -/
axiom mycielski_construction :
  ∀ k : ℕ, k ≥ 2 → ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
    IsTriangleFree G ∧ ¬HasProperColoring G (k - 1)
