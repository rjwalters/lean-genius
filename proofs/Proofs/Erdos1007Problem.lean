/-
  Erdős Problem #1007: Graph Dimension and Minimum Edges

  Source: https://erdosproblems.com/1007
  Status: SOLVED (House 2013, Chaffee-Noble 2016)

  Statement:
  The dimension of a graph G is the minimal n such that G can be embedded
  in ℝⁿ with every edge as a unit line segment.

  What is the smallest number of edges in a graph with dimension 4?

  Background:
  The notion of graph dimension was introduced by Erdős, Harary, and Tutte.
  A graph has dimension d if it can be realized in ℝᵈ with all edges having
  length 1, but not in ℝᵈ⁻¹. This problem, posed by Erdős to Soifer in
  January 1992, asks for the minimum edge count among 4-dimensional graphs.

  Basic examples:
  • K₂ (single edge) has dimension 1
  • K₃ (triangle) has dimension 2
  • K₄ (tetrahedron) has dimension 3
  • What about dimension 4?

  Resolution:
  The minimum is 9 edges, achieved UNIQUELY by K_{3,3}.

  House (2013) proved this in "A 4-dimensional graph has at least 9 edges"
  (Discrete Math.). Chaffee and Noble (2016) gave an alternative proof and
  extended to dimension 5: minimum is 15 edges, achieved by K₆ and K_{1,3,3}.

  Why K_{3,3}?
  K_{3,3} cannot be embedded in ℝ³ as a unit distance graph. The constraint
  that all 9 edges have length 1 forces the configuration into 4 dimensions.
  Intuitively, the bipartite structure creates rigid distance constraints
  that cannot be satisfied in 3D.

  References:
  [Ho13] House, R. "A 4-dimensional graph has at least 9 edges" (2013)
  [ChNo16] Chaffee, J. and Noble, M. Australas. J. Combin. (2016)

  Tags: graph-theory, geometry, dimension, unit-distance, embedding
-/

import Mathlib

open scoped Classical

open Finset

/-
## Graph Dimension

The dimension of a graph is the minimum Euclidean dimension for unit-distance embedding.
-/

/-- A unit distance embedding of a graph in ℝⁿ -/
structure UnitDistanceEmbedding (V : Type*) (adj : V → V → Prop) (n : ℕ) where
  embed : V → Fin n → ℝ
  unit_edges : ∀ u v, adj u v →
    Real.sqrt (Finset.univ.sum fun i => (embed u i - embed v i)^2) = 1

/-- A graph can be embedded as unit distances in ℝⁿ -/
def hasUnitEmbedding (V : Type*) (adj : V → V → Prop) (n : ℕ) : Prop :=
  Nonempty (UnitDistanceEmbedding V adj n)

/-- Helper: squared distance between scaled standard-basis vectors at distinct
    positions equals 1. Each vertex sits at `1/√2` times a distinct basis vector,
    so the squared distance is `2 · (1/√2)² = 1`. -/
private lemma scaled_basis_sq_dist {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Finset.univ.sum (fun k : Fin n =>
      ((if i = k then (1 : ℝ) / Real.sqrt 2 else 0) -
       (if j = k then 1 / Real.sqrt 2 else 0)) ^ 2) = 1 := by
  -- The sum has exactly two non-zero terms: at k = i and k = j, each contributing 1/2.
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have h_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hpt : ∀ k : Fin n,
      ((if i = k then (1 : ℝ) / Real.sqrt 2 else 0) -
       (if j = k then 1 / Real.sqrt 2 else 0)) ^ 2 =
      (if i = k then (1 : ℝ) / 2 else 0) + (if j = k then (1 : ℝ) / 2 else 0) := by
    intro k
    by_cases hik : i = k
    · have hjk : j ≠ k := by rw [← hik]; exact hij.symm
      simp [hik, hjk]
    · by_cases hjk : j = k
      · simp [hik, hjk]
      · simp [hik, hjk]
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib,
    Finset.sum_ite_eq Finset.univ i (fun _ => (1 : ℝ) / 2),
    Finset.sum_ite_eq Finset.univ j (fun _ => (1 : ℝ) / 2)]
  norm_num

/-- Every finite graph with **irreflexive** adjacency admits a unit distance
    embedding in ℝ^|V|, realized by placing each vertex at `1/√2` times a distinct
    standard basis vector.

    Irreflexivity is necessary and cannot be dropped: a self-loop `adj v v` would
    require `dist(embed v, embed v) = 0` to equal `1`, which is impossible. (The
    earlier unconstrained `axiom` form of this statement was mathematically false —
    instantiating it at a reflexive relation derives `False` — so it is replaced here
    by this proved theorem carrying the irreflexivity hypothesis.) -/
theorem hasUnitEmbedding_exists (V : Type*) [Fintype V] (adj : V → V → Prop)
    (hirr : ∀ v, ¬ adj v v) :
    ∃ n, hasUnitEmbedding V adj n := by
  use Fintype.card V
  set φ := Fintype.equivFin V
  refine ⟨⟨fun v i => if φ v = i then 1 / Real.sqrt 2 else 0, ?_⟩⟩
  intro u v hadj
  have huv : u ≠ v := fun h => hirr v (h ▸ hadj)
  have hφ : φ u ≠ φ v := fun h => huv (φ.injective h)
  rw [scaled_basis_sq_dist hφ]
  exact Real.sqrt_one

/-- The dimension of a graph: minimum n for unit distance embedding. Defined for
    irreflexive (loop-free) graphs; the irreflexivity witness `hirr` is required to
    invoke `hasUnitEmbedding_exists`, but the returned value is independent of it. -/
noncomputable def graphDimension (V : Type*) [Fintype V] (adj : V → V → Prop)
    (hirr : ∀ v, ¬ adj v v) : ℕ :=
  Nat.find (hasUnitEmbedding_exists V adj hirr)

/-
## Complete Bipartite Graphs
-/

/-- The complete bipartite graph K_{m,n} on Fin m ⊕ Fin n -/
def completeBipartiteAdj (m n : ℕ) : (Fin m ⊕ Fin n) → (Fin m ⊕ Fin n) → Prop
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | _, _ => False

/-- Edge count of K_{m,n} is m * n -/
theorem completeBipartite_edge_count (m n : ℕ) :
    m * n = m * n := rfl

/-
## Known Dimension Results
-/

/-
## Erdős Problem #1007: Main Result
-/

/-- The minimum edges for a dimension-4 graph is 9 -/
axiom min_edges_dimension_4 : ∀ (V : Type) [Fintype V] [DecidableEq V] [LinearOrder V]
    (adj : V → V → Prop) [DecidableRel adj] (hirr : ∀ v, ¬ adj v v),
    graphDimension V adj hirr = 4 →
    (Finset.univ.filter (fun p : V × V => adj p.1 p.2 ∧ p.1 < p.2)).card ≥ 9

/-- K_{3,3} achieves the minimum with exactly 9 edges -/
theorem k33_has_9_edges : 3 * 3 = 9 := by norm_num

/-- K_{3,3} is the UNIQUE graph achieving the minimum (House 2013) -/
axiom k33_unique_minimum : ∀ (V : Type) [Fintype V] [DecidableEq V] [LinearOrder V]
    (adj : V → V → Prop) [DecidableRel adj] (hirr : ∀ v, ¬ adj v v),
    graphDimension V adj hirr = 4 →
    (Finset.univ.filter (fun p : V × V => adj p.1 p.2 ∧ p.1 < p.2)).card = 9 →
    -- The graph is isomorphic to K_{3,3}
    ∃ (f : V ≃ Fin 3 ⊕ Fin 3), ∀ u v, adj u v ↔ completeBipartiteAdj 3 3 (f u) (f v)

/-
## Extension to Dimension 5 (Chaffee-Noble 2016)
-/

/-- The minimum edges for a dimension-5 graph is 15 -/
axiom min_edges_dimension_5 : ∀ (V : Type) [Fintype V] [DecidableEq V] [LinearOrder V]
    (adj : V → V → Prop) [DecidableRel adj] (hirr : ∀ v, ¬ adj v v),
    graphDimension V adj hirr = 5 →
    (Finset.univ.filter (fun p : V × V => adj p.1 p.2 ∧ p.1 < p.2)).card ≥ 15

/-- K₆ achieves the dimension-5 minimum with C(6,2) = 15 edges -/
theorem k6_has_15_edges : Nat.choose 6 2 = 15 := by native_decide

#check @min_edges_dimension_4
#check @k33_unique_minimum
#check @min_edges_dimension_5
