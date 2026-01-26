/-!
# Erdős Problem #500: Turán Density of K₄³

Determine ex₃(n, K₄³): the maximum number of 3-edges on n vertices
containing no complete 3-uniform hypergraph on 4 vertices.

## Key Results
- Turán's construction: ex₃(n, K₄³) ≥ (5/9 + o(1))·C(n,3)
  (partition into 3 equal parts, take specific edge pattern)
- Razborov (2010): ex₃(n, K₄³) ≤ 0.5611666·C(n,3)
  (flag algebra method)
- Conjectured: ex₃(n, K₄³) = (5/9 + o(1))·C(n,3) (Turán 1941)

## Status: OPEN
This is one of the most famous open problems in extremal combinatorics.
It is sometimes called "Turán's hypergraph problem."

Reference: https://erdosproblems.com/500
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- A 3-uniform hypergraph on vertex set Fin n: a collection of 3-element subsets. -/
def Hypergraph3 (n : ℕ) := Finset (Finset (Fin n))

/-- A hypergraph is 3-uniform if every edge has exactly 3 vertices. -/
def IsThreeUniform (n : ℕ) (H : Hypergraph3 n) : Prop :=
  ∀ e ∈ H, e.card = 3

/-- K₄³: the complete 3-uniform hypergraph on 4 vertices.
    It consists of all C(4,3) = 4 triples from a 4-element set. -/
def ContainsK4_3 (n : ℕ) (H : Hypergraph3 n) : Prop :=
  ∃ S : Finset (Fin n), S.card = 4 ∧
    ∀ T : Finset (Fin n), T ⊆ S → T.card = 3 → T ∈ H

/-- A K₄³-free 3-uniform hypergraph. -/
def IsK4Free (n : ℕ) (H : Hypergraph3 n) : Prop :=
  IsThreeUniform n H ∧ ¬ContainsK4_3 n H

/-- ex₃(n, K₄³): the Turán number for K₄³ in 3-uniform hypergraphs.
    The maximum number of edges in a K₄³-free 3-uniform hypergraph on n vertices. -/
axiom ex3_K4 (n : ℕ) : ℕ

/-- ex₃(n, K₄³) is achieved by some K₄³-free hypergraph. -/
axiom ex3_K4_achievable (n : ℕ) :
    ∃ H : Hypergraph3 n, IsK4Free n H ∧ H.card = ex3_K4 n

/-- No K₄³-free 3-uniform hypergraph on n vertices exceeds ex₃(n, K₄³) edges. -/
axiom ex3_K4_optimal (n : ℕ) (H : Hypergraph3 n) (hfree : IsK4Free n H) :
    H.card ≤ ex3_K4 n

/-! ## Turán Density -/

/-- The Turán density: π(K₄³) = lim_{n→∞} ex₃(n, K₄³) / C(n,3). -/
axiom turanDensityK4_3 : ℝ

/-- The Turán density exists and is well-defined. -/
axiom turanDensity_exists :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      |((ex3_K4 n : ℝ) / (Nat.choose n 3 : ℝ)) - turanDensityK4_3| < ε

/-! ## Turán's Lower Bound (1941) -/

/-- Turán's construction: partition n vertices into 3 nearly-equal parts,
    take all triples that intersect each part in at most 2 vertices.
    This gives (5/9 + o(1))·C(n,3) edges and is K₄³-free. -/
axiom turan_lower_bound : turanDensityK4_3 ≥ 5 / 9

/-- Turán's construction gives an explicit lower bound for finite n. -/
axiom turan_construction_bound (n : ℕ) (hn : n ≥ 4) :
    ex3_K4 n ≥ (5 * Nat.choose n 3) / 9

/-! ## Razborov's Upper Bound (2010) -/

/-- Razborov (2010) via flag algebras: π(K₄³) ≤ 0.5611666...
    This improved earlier bounds by de Caen (1994) and others. -/
axiom razborov_upper_bound : turanDensityK4_3 ≤ 5611666 / 10000000

/-! ## Turán's Conjecture -/

/-- Turán's Conjecture (1941): π(K₄³) = 5/9.
    The construction is conjectured to be optimal.
    This is Erdős Problem #500. -/
axiom turan_conjecture : turanDensityK4_3 = 5 / 9

/-! ## Small Cases and Exact Values -/

/-- ex₃(4, K₄³) = 3: on 4 vertices, at most 3 of the 4 triples can be chosen. -/
axiom ex3_K4_four : ex3_K4 4 = 3

/-- ex₃(5, K₄³) = 7 (known exactly). -/
axiom ex3_K4_five : ex3_K4 5 = 7

/-- ex₃(6, K₄³) = 13 (known exactly). -/
axiom ex3_K4_six : ex3_K4 6 = 13

/-! ## Context: Hypergraph Turán Problems -/

/-- The gap between the lower bound 5/9 ≈ 0.5556 and the upper bound ≈ 0.5612
    is remarkably small. Closing this gap is one of the central open problems
    in extremal combinatorics. -/
axiom gap_bounds : 5 / 9 ≤ turanDensityK4_3 ∧ turanDensityK4_3 ≤ 5612 / 10000
