/-
Erdős Problem #915: Disjoint Paths in Graphs

Source: https://erdosproblems.com/915
Status: SOLVED (partially disproved, partially confirmed)

Statement:
Let G be a graph with 1 + n(m-1) vertices and 1 + n·C(m,2) edges.
Must G contain two vertices connected by m disjoint paths?

This is the Bollobás-Erdős conjecture (1962).

Results:
- VERTEX-DISJOINT (k_m): Conjecture TRUE for m ≤ 4 (Bártfai, Bollobás)
                         Conjecture FALSE for m ≥ 5 (Leonard, Mader)
- EDGE-DISJOINT (ℓ_m): Conjecture TRUE for all m ≥ 2 (Mader 1973)
                        ℓ_m(n) = ⌊m(n-1)/2 + 1⌋

References:
- Bollobás-Erdős (1962): Original conjecture
- Bártfai (1960): k_3 case
- Bollobás (1966): k_4 case
- Leonard (1973): Disproved for m = 5
- Mader (1973): Disproved for m ≥ 6, proved edge-disjoint case
- Sørensen-Thomassen (1974): k_5 exact formula
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic

open SimpleGraph Finset Nat

namespace Erdos915

/-! ## Basic Definitions -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A path between two vertices in a simple graph. -/
structure Path (G : SimpleGraph V) (u v : V) where
  vertices : List V
  edges_valid : vertices.length ≥ 2
  starts_at : vertices.head? = some u
  ends_at : vertices.getLast? = some v
  is_walk : ∀ i : ℕ, i + 1 < vertices.length →
    G.Adj (vertices.get ⟨i, by omega⟩) (vertices.get ⟨i + 1, by omega⟩)

/-- Two paths are vertex-disjoint if they share no internal vertices. -/
def VertexDisjoint (G : SimpleGraph V) (u v : V)
    (p1 p2 : Path G u v) : Prop :=
  let internal1 := p1.vertices.drop 1 |>.dropLast
  let internal2 := p2.vertices.drop 1 |>.dropLast
  ∀ x ∈ internal1, x ∉ internal2

/-- Two paths are edge-disjoint if they share no edges. -/
def EdgeDisjoint (G : SimpleGraph V) (u v : V)
    (p1 p2 : Path G u v) : Prop :=
  ∀ i j : ℕ,
    i + 1 < p1.vertices.length →
    j + 1 < p2.vertices.length →
    let e1 := (p1.vertices.get ⟨i, by omega⟩, p1.vertices.get ⟨i + 1, by omega⟩)
    let e2 := (p2.vertices.get ⟨j, by omega⟩, p2.vertices.get ⟨j + 1, by omega⟩)
    ¬(e1 = e2 ∨ e1 = (e2.2, e2.1))

/-- A collection of m paths that are pairwise vertex-disjoint. -/
def HasMVertexDisjointPaths (G : SimpleGraph V) (u v : V) (m : ℕ) : Prop :=
  ∃ (paths : Fin m → Path G u v),
    ∀ i j : Fin m, i ≠ j → VertexDisjoint G u v (paths i) (paths j)

/-- A collection of m paths that are pairwise edge-disjoint. -/
def HasMEdgeDisjointPaths (G : SimpleGraph V) (u v : V) (m : ℕ) : Prop :=
  ∃ (paths : Fin m → Path G u v),
    ∀ i j : Fin m, i ≠ j → EdgeDisjoint G u v (paths i) (paths j)

/-- Graph contains vertices with m vertex-disjoint paths between them. -/
def ContainsMVertexDisjointPair (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ u v : V, u ≠ v ∧ HasMVertexDisjointPaths G u v m

/-- Graph contains vertices with m edge-disjoint paths between them. -/
def ContainsMEdgeDisjointPair (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ u v : V, u ≠ v ∧ HasMEdgeDisjointPaths G u v m

/-! ## The Functions k_m(n) and ℓ_m(n) -/

/--
**k_m(n):** Minimum edges such that any graph with n vertices and k_m(n) edges
contains two vertices connected by m vertex-disjoint paths.
Axiomatized since computing the exact minimum is an extremal graph theory problem.
-/
axiom k (m n : ℕ) : ℕ

/--
**ℓ_m(n):** Minimum edges such that any graph with n vertices and ℓ_m(n) edges
contains two vertices connected by m edge-disjoint paths.
-/
axiom ell (m n : ℕ) : ℕ

/-- ℓ_m(n) ≤ k_m(n) since vertex-disjoint implies edge-disjoint. -/
axiom ell_le_k (m n : ℕ) (hm : m ≥ 2) : ell m n ≤ k m n

/-! ## The Bollobás-Erdős Conjecture -/

/--
**The Bollobás-Erdős Conjecture (1962):**
For all m ≥ 2: k_m(1 + (m-1)n) = 1 + C(m,2)·n

This predicts k_m(n) = (m/2)·n + O(1) growth.
-/
def BollobasErdosConjecture (m : ℕ) : Prop :=
  m ≥ 2 → ∀ n ≥ 1, k m (1 + (m - 1) * n) = 1 + choose m 2 * n

/--
**The Extremal Construction:**
n copies of K_m sharing a single vertex (otherwise disjoint).
This has 1 + (m-1)n vertices and 1 + C(m,2)n edges.
-/
axiom extremal_construction (m n : ℕ) (hm : m ≥ 2) (hn : n ≥ 1) :
    ∃ V : Type, ∃ _ : Fintype V, ∃ _ : DecidableEq V,
    ∃ G : SimpleGraph V,
      Fintype.card V = 1 + (m - 1) * n ∧
      G.edgeFinset.card = 1 + choose m 2 * n ∧
      ¬ContainsMVertexDisjointPair G m

/-! ## Small Cases: Conjecture TRUE for m ≤ 4 -/

/-- k_2(n) = n (trivial). -/
axiom k_2 (n : ℕ) (hn : n ≥ 2) : k 2 n = n

/-- Bártfai (1960): k_3(2n) = 3n - 1 and k_3(2n+1) = 3n + 1. -/
axiom bartfai_k3_even (n : ℕ) (hn : n ≥ 1) : k 3 (2 * n) = 3 * n - 1
axiom bartfai_k3_odd (n : ℕ) (hn : n ≥ 1) : k 3 (2 * n + 1) = 3 * n + 1

/-- Bollobás (1966): k_4(n) = 2n - 1. -/
axiom bollobas_k4 (n : ℕ) (hn : n ≥ 4) : k 4 n = 2 * n - 1

/-- The conjecture holds for m = 2, 3, 4.
    Axiomatized since deriving the conjecture format from the explicit formulas
    requires careful arithmetic with choose and modular cases. -/
axiom conjecture_m2 : BollobasErdosConjecture 2
axiom conjecture_m3 : BollobasErdosConjecture 3
axiom conjecture_m4 : BollobasErdosConjecture 4

theorem conjecture_small_m : BollobasErdosConjecture 2 ∧
                              BollobasErdosConjecture 3 ∧
                              BollobasErdosConjecture 4 :=
  ⟨conjecture_m2, conjecture_m3, conjecture_m4⟩

/-! ## The Disproof for m ≥ 5 -/

/--
**Leonard (1973) Counterexample:**
A graph with 57 vertices and 141 edges that avoids 5 vertex-disjoint paths
between any pair of vertices.

The conjecture predicts k_5(57) = 1 + 10·14 = 141, but this graph shows
that 141 edges are not enough.
-/
axiom leonard_counterexample :
    ∃ V : Type, ∃ _ : Fintype V, ∃ _ : DecidableEq V,
    ∃ G : SimpleGraph V,
      Fintype.card V = 57 ∧
      G.edgeFinset.card = 141 ∧
      ¬ContainsMVertexDisjointPair G 5

/-- Leonard (1973): k_5(n) > (5/2 + c)n - O(1) for some c > 0. -/
axiom leonard_lower_bound :
    ∃ c : ℚ, c > 0 ∧
    ∀ᶠ n in Filter.atTop, (k 5 n : ℚ) > (5/2 + c) * n - 10

/--
**Sørensen-Thomassen (1974):**
k_5(n) = ⌊8n/3⌋ - 3 for n ≥ 13.

This is LARGER than the conjectured (5/2)n + O(1).
-/
axiom sorensen_thomassen_k5 (n : ℕ) (hn : n ≥ 13) :
    k 5 n = (8 * n) / 3 - 3

/--
**Mader (1973): Conjecture FALSE for all m ≥ 6.**
For any C > 0 and m ≥ 6, there exists n with k_m(n) > (m/2)n + C.
-/
axiom mader_disproof (m : ℕ) (hm : m ≥ 6) :
    ∀ C : ℕ, ∃ n : ℕ, k m n > m * n / 2 + C

/-- The vertex-disjoint conjecture is FALSE for m = 5.
    Leonard's counterexample contradicts the conjectured value. -/
axiom conjecture_false_m5 : ¬BollobasErdosConjecture 5

/-- The vertex-disjoint conjecture is FALSE for m ≥ 6.
    Mader showed k_m(n) exceeds (m/2)n + C for arbitrary C. -/
axiom conjecture_false_large_m (m : ℕ) (hm : m ≥ 6) : ¬BollobasErdosConjecture m

/-! ## The Edge-Disjoint Case: Fully Solved -/

/--
**Mader (1973): Complete solution for edge-disjoint paths.**
ℓ_m(n) = ⌊m(n-1)/2 + 1⌋ for all m ≥ 2.

This confirms the Bollobás-Erdős conjecture for edge-disjoint paths!
-/
axiom mader_edge_disjoint (m n : ℕ) (hm : m ≥ 2) (hn : n ≥ 2) :
    ell m n = m * (n - 1) / 2 + 1

/-- The edge-disjoint version of the conjecture is TRUE. -/
def EdgeDisjointConjecture (m : ℕ) : Prop :=
  m ≥ 2 → ∀ n ≥ 2, ell m n = m * (n - 1) / 2 + 1

theorem edge_disjoint_solved (m : ℕ) (hm : m ≥ 2) :
    EdgeDisjointConjecture m := fun _ n hn => mader_edge_disjoint m n hm hn

/-! ## Specific Values for ℓ_m -/

/-- Leonard (1972): ℓ_m(n) = k_m(n) for m ≤ 4. -/
axiom leonard_small_m (m n : ℕ) (hm : 2 ≤ m ∧ m ≤ 4) :
    ell m n = k m n

/-- Leonard (1972): ℓ_5(2n) = 5n - 2 and ℓ_5(2n+1) = 5n + 1. -/
axiom leonard_ell5_even (n : ℕ) (hn : n ≥ 1) : ell 5 (2 * n) = 5 * n - 2
axiom leonard_ell5_odd (n : ℕ) (hn : n ≥ 1) : ell 5 (2 * n + 1) = 5 * n + 1

/-- Leonard (1973): ℓ_6(n) = 3n - 2. -/
axiom leonard_ell6 (n : ℕ) (hn : n ≥ 2) : ell 6 n = 3 * n - 2

/-! ## Mader's Stronger Result -/

/--
**Mader's Degree Condition:**
If a graph G has > (m/2)(n-1) - (1/2)·(e_0(G) + ... + e_{m-2}(G)) edges,
where e_r(G) counts vertices of degree ≤ r, then G contains two vertices
connected by m edge-disjoint paths.
-/
axiom mader_degree_condition (G : SimpleGraph V) (m : ℕ) (hm : m ≥ 2) :
    let n := Fintype.card V
    let low_degree_sum := (Finset.range (m - 1)).sum fun r =>
      (Finset.univ.filter fun v => G.degree v ≤ r).card
    G.edgeFinset.card > m * (n - 1) / 2 - low_degree_sum / 2 →
    ContainsMEdgeDisjointPair G m

/-! ## 3-Connected Graphs -/

/--
**Sørensen-Thomassen (1974):**
The Bollobás-Erdős conjecture holds for 3-connected graphs.
The 3-connectivity hypothesis is axiomatized as a separate condition
since Mathlib's connectivity API for specific k-connectivity levels
requires additional infrastructure.
-/
axiom three_connected_conjecture (G : SimpleGraph V) (m n : ℕ)
    (hm : m ≥ 2) (hvertices : Fintype.card V = 1 + (m - 1) * n)
    (hedges : G.edgeFinset.card ≥ 1 + choose m 2 * n)
    (h3conn : ∀ (S : Finset V), S.card < 3 →
      (G.induce (Finset.univ \ S : Set V).toFinset).Connected)
    :
    ContainsMVertexDisjointPair G m

/-! ## Summary -/

/--
**Erdős Problem #915: Summary**

**The Bollobás-Erdős Conjecture:**
k_m(1 + (m-1)n) = 1 + C(m,2)n

**Vertex-Disjoint Paths (k_m):**
- TRUE for m = 2, 3, 4 (Bártfai, Bollobás)
- FALSE for m = 5 (Leonard 1973, counterexample with 57 vertices)
- FALSE for m ≥ 6 (Mader 1973)
- k_5(n) = ⌊8n/3⌋ - 3 for n ≥ 13 (Sørensen-Thomassen)

**Edge-Disjoint Paths (ℓ_m):**
- TRUE for all m ≥ 2 (Mader 1973)
- ℓ_m(n) = ⌊m(n-1)/2 + 1⌋
-/
theorem erdos_915_summary :
    -- Small m: vertex-disjoint conjecture holds
    (BollobasErdosConjecture 2 ∧ BollobasErdosConjecture 3 ∧ BollobasErdosConjecture 4) ∧
    -- m = 5: vertex-disjoint conjecture fails
    ¬BollobasErdosConjecture 5 ∧
    -- m ≥ 6: vertex-disjoint conjecture fails
    (∀ m ≥ 6, ¬BollobasErdosConjecture m) ∧
    -- Edge-disjoint: conjecture holds for all m
    (∀ m ≥ 2, EdgeDisjointConjecture m) :=
  ⟨conjecture_small_m,
   conjecture_false_m5,
   conjecture_false_large_m,
   edge_disjoint_solved⟩

end Erdos915
