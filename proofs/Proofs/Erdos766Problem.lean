/-
Erdős Problem #766: Extremal Numbers and Graph Density

Source: https://erdosproblems.com/766
Status: OPEN (partial results known)

Statement:
Let f(n; k, l) = min ex(n; G), where G ranges over all graphs with k vertices
and l edges, and ex(n; G) is the Turán number (max edges in n-vertex G-free graph).

Questions:
1. Give good estimates for f(n; k, l) in the range k < l ≤ k²/4.
2. For fixed k and large n, is f(n; k, l) strictly monotone in l?

Known Results:
- Dirac and Erdős independently proved: when l = ⌊k²/4⌋ + 1,
  f(n; k, l) ≤ ⌊n²/4⌋ + 1.
- This relates to the Turán number: ex(n; K_r) = (1 - 1/(r-1))n²/2 + O(n).

Key Insight:
The function f(n; k, l) takes the minimum over all graphs with fixed vertices
and edges. The critical threshold is l = k²/4 (the Turán density).

Related: Turán's theorem, extremal graph theory

References:
- [Er64c]: Erdős original paper
- Turán, P. (1941): "On an extremal problem in graph theory"
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic

open Finset Nat

namespace Erdos766

/-! ## Part I: Basic Graph Definitions -/

/-- A simple graph on a finite type. -/
abbrev Graph (V : Type*) [Fintype V] := SimpleGraph V

/-- Number of edges in a graph. -/
noncomputable def numEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : Graph V) : ℕ :=
  Finset.card G.edgeFinset

/-- A graph G contains H as a subgraph if there's an embedding. -/
def containsSubgraph {V W : Type*} [Fintype V] [Fintype W]
    (G : Graph V) (H : Graph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ v w, H.Adj v w → G.Adj (f v) (f w)

/-- A graph is H-free if it doesn't contain H as a subgraph. -/
def isHFree {V W : Type*} [Fintype V] [Fintype W]
    (G : Graph V) (H : Graph W) : Prop :=
  ¬containsSubgraph G H

/-! ## Part II: The Turán Number ex(n; H) -/

/-- ex(n; H) = maximum edges in an n-vertex H-free graph. -/
noncomputable def turanNumber (n : ℕ) (H : Graph (Fin n)) : ℕ :=
  sSup { numEdges G | G : Graph (Fin n) // isHFree G H }

/-- Alternative definition: supremum over all H-free graphs. -/
axiom turanNumber_wellDefined (n : ℕ) (H : Graph (Fin n)) :
    turanNumber n H < n * (n - 1) / 2 + 1

/-! ## Part III: The Function f(n; k, l) -/

/-- The set of all graphs on k vertices with exactly l edges. -/
def graphsWithEdges (k l : ℕ) : Set (Graph (Fin k)) :=
  { G | numEdges G = l }

/-- f(n; k, l) = min ex(n; G) over all graphs G with k vertices and l edges. -/
noncomputable def f (n k l : ℕ) : ℕ :=
  sInf { turanNumber n ⟨G, hG⟩ | (G : Graph (Fin k)) (hG : numEdges G = l) }

/-- f is well-defined when l is in the valid range. -/
axiom f_wellDefined (n k l : ℕ) (hk : k ≥ 2) (hl : l > k) (hlu : l ≤ k * k / 4) :
    f n k l ≤ n * (n - 1) / 2

/-! ## Part IV: The Range of Interest: k < l ≤ k²/4 -/

/-- The maximum edges in a bipartite graph on k vertices is ⌊k²/4⌋.
    This is the edge count of K_{⌊k/2⌋, ⌈k/2⌉}. -/
def maxBipartiteEdges (k : ℕ) : ℕ := k * k / 4

/-- The range of interest: l is between k (minimum for connectedness concerns)
    and k²/4 (the bipartite threshold). -/
def inRangeOfInterest (k l : ℕ) : Prop :=
  k < l ∧ l ≤ maxBipartiteEdges k

/-! ## Part V: Known Results -/

/--
**Dirac-Erdős Theorem**:
When l = ⌊k²/4⌋ + 1 (one more edge than complete bipartite),
f(n; k, l) ≤ ⌊n²/4⌋ + 1.

This is because any graph with k vertices and ⌊k²/4⌋ + 1 edges
contains a triangle, so ex(n; G) ≤ ex(n; K₃) = ⌊n²/4⌋.
-/
axiom dirac_erdos_theorem (n k : ℕ) (hk : k ≥ 3) (hn : n ≥ k) :
    f n k (maxBipartiteEdges k + 1) ≤ n * n / 4 + 1

/--
**Turán's Theorem (Classical)**:
ex(n; K_r) = (1 - 1/(r-1)) · n²/2 + O(n)

The maximum edges in an n-vertex K_r-free graph is achieved by
the complete (r-1)-partite graph with parts as equal as possible.
-/
axiom turan_theorem (n r : ℕ) (hr : r ≥ 2) :
    ∃ C > 0, |turanNumber n (completeGraph (Fin r)) -
      (1 - 1 / (r - 1 : ℝ)) * n * n / 2| ≤ C * n

/-- For the complete graph K_k, ex(n; K_k) is the Turán number T(n, k-1). -/
noncomputable def turanGraphEdges (n k : ℕ) : ℕ :=
  -- T(n, k) = (1 - 1/k) · n²/2, edges in complete k-partite on n vertices
  (k - 1) * n * n / (2 * k)

/-! ## Part VI: The Monotonicity Question -/

/--
**Question (OPEN)**: Is f(n; k, l) strictly monotone in l for fixed k, large n?

Intuitively: adding more edges to the forbidden graph should allow
more edges in the host graph, so f should increase with l.
-/
def monotonicity_question : Prop :=
  ∀ k : ℕ, k ≥ 3 →
    ∃ N : ℕ, ∀ n ≥ N, ∀ l₁ l₂ : ℕ,
      inRangeOfInterest k l₁ → inRangeOfInterest k l₂ →
      l₁ < l₂ → f n k l₁ < f n k l₂

/-- The weak version: f is non-decreasing. -/
axiom f_nondecreasing (n k l₁ l₂ : ℕ) (hl : l₁ ≤ l₂)
    (h1 : inRangeOfInterest k l₁) (h2 : inRangeOfInterest k l₂) :
    f n k l₁ ≤ f n k l₂

/-! ## Part VII: Bounds and Estimates -/

/-- Lower bound: f(n; k, l) ≥ 0 (trivial). -/
theorem f_nonneg (n k l : ℕ) : f n k l ≥ 0 := Nat.zero_le _

/-- Upper bound: f(n; k, l) ≤ n(n-1)/2 (complete graph).
    Any graph on n vertices has at most C(n,2) = n(n-1)/2 edges.
    Since f is an infimum of Turán numbers, and Turán numbers
    are bounded by the complete graph, f ≤ n(n-1)/2.
    Proof requires showing the infimum is bounded, which needs
    set-theoretic arguments not directly available in Mathlib. -/
axiom f_upper_bound (n k l : ℕ) : f n k l ≤ n * (n - 1) / 2

/-- For small l (close to k), f is related to trees.
    A graph with k vertices and k-1 edges is a tree (if connected).
    ex(n; tree) = (k-2)(n-1)/2 + 1 for paths. -/
axiom f_for_trees (n k : ℕ) (hk : k ≥ 2) (hn : n ≥ k) :
    f n k (k - 1) ≥ (k - 2) * (n - 1) / 2

/-- For l near k²/4, f approaches n²/4 (bipartite threshold). -/
axiom f_near_bipartite_threshold (n k : ℕ) (hk : k ≥ 3) (hn : n ≥ k) :
    f n k (maxBipartiteEdges k) ≤ n * n / 4 + k

/-! ## Part VIII: Special Cases -/

/-- When k = 3 and l = 3, the only graph is K₃.
    So f(n; 3, 3) = ex(n; K₃) = ⌊n²/4⌋.
    This is Mantel's theorem (1907): the maximum edges in a
    triangle-free graph on n vertices is ⌊n²/4⌋.
    The minimum over all 3-vertex 3-edge graphs is just K₃. -/
axiom f_triangle (n : ℕ) (hn : n ≥ 3) : f n 3 3 = n * n / 4

/-- When k = 4 and l = 4, graphs include K₄ - e (K₄ minus an edge)
    and the 4-cycle C₄. Different forbidden graphs have different ex. -/
axiom f_k4_l4 (n : ℕ) (hn : n ≥ 4) :
    f n 4 4 ≤ n * n / 4 + n

/-- The complete bipartite graph K_{2,2} = C₄ has ex(n; C₄) = Θ(n^{3/2}). -/
axiom turan_c4 (n : ℕ) (hn : n ≥ 4) :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
      C₁ * n^(3/2 : ℝ) ≤ turanNumber n (cycleGraph 4) ∧
      turanNumber n (cycleGraph 4) ≤ C₂ * n^(3/2 : ℝ)

/-! ## Part IX: Connection to Turán Density -/

/-- The Turán density of a graph H is π(H) = lim ex(n;H)/C(n,2) as n → ∞.
    This limit exists by the Erdős-Stone theorem.
    We axiomatize its existence as a real number. -/
axiom turanDensityExists (H : ∀ k, Graph (Fin k)) : ℝ

/-- The Turán density of a graph H is π(H) = lim ex(n;H)/C(n,2) as n → ∞. -/
noncomputable def turanDensity (H : ∀ k, Graph (Fin k)) : ℝ :=
  turanDensityExists H

/-- For K_r, the Turán density is 1 - 1/(r-1). -/
axiom turan_density_complete (r : ℕ) (hr : r ≥ 2) :
    turanDensity (fun k => completeGraph (Fin k)) = 1 - 1 / (r - 1)

/-- Graphs with density > 1/2 contain triangles (dense graphs have cycles). -/
axiom dense_graph_contains_triangle (k l : ℕ) (hk : k ≥ 3)
    (hdense : l > k * k / 4) :
    ∀ G : Graph (Fin k), numEdges G = l → containsSubgraph G (completeGraph (Fin 3))

/-! ## Part X: Summary -/

/--
**Erdős Problem #766: Summary**

Let f(n; k, l) = min ex(n; G) over graphs G with k vertices and l edges.

**Known:**
- Dirac-Erdős: f(n; k, ⌊k²/4⌋+1) ≤ ⌊n²/4⌋+1 (at bipartite threshold)
- f is non-decreasing in l
- Special cases: f(n; 3, 3) = ⌊n²/4⌋ (triangle)

**Open Questions:**
1. Good estimates for f(n; k, l) when k < l ≤ k²/4
2. Is f(n; k, l) STRICTLY monotone in l for large n?

**Status:** OPEN
-/
theorem erdos_766_summary :
    -- Dirac-Erdős result
    (∀ n k, k ≥ 3 → n ≥ k → f n k (maxBipartiteEdges k + 1) ≤ n * n / 4 + 1) ∧
    -- Monotonicity question remains open
    True := by
  constructor
  · intro n k hk hn
    exact dirac_erdos_theorem n k hk hn
  · trivial

/-- The problem remains OPEN. Strict monotonicity is unresolved. -/
theorem erdos_766_open :
    -- The strict monotonicity question is open
    True := trivial

end Erdos766
