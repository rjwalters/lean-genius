/-
  Erdős Problem #549: Ramsey Numbers for Bipartite Trees

  Source: https://erdosproblems.com/549
  Status: SOLVED (Disproved)

  Original Conjecture:
  If T is a tree which is bipartite with k vertices in one class and
  2k vertices in the other class, then R(T) = 4k - 1.

  Resolution:
  The conjecture is FALSE!
  - Norin-Sun-Zhao: R(T) ≥ (4.2 - o(1))k for the "double star" tree
  - Upper bound: R(T) ≤ (4.21526 + o(1))k via flag algebras
  - Special cases (bounded degree, brooms) still satisfy R(T) = 4k - 1

  The double star counterexample:
  Connect the centers of a k-star and a 2k-star. This tree has exactly
  k vertices in one class (the k leaves + 2k-star center) and... wait,
  let me reconsider: the tree is S_k ∪ S_{2k} with centers joined.

  Related: Problems #550, #551 (other tree Ramsey problems)
-/

import Mathlib

open Finset Function Set SimpleGraph

/-! ## Trees and Bipartite Graphs -/

/-- A tree is a connected acyclic graph -/
def IsTree {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ G.IsAcyclic

/-- A graph is bipartite with parts A and B -/
def IsBipartiteWith {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  A ∩ B = ∅ ∧
  A ∪ B = Set.univ ∧
  ∀ u v : V, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)

/-- A tree with bipartition (k, 2k) -/
structure BipartiteTree (k : ℕ) where
  V : Type*
  [finV : Fintype V]
  [decV : DecidableEq V]
  graph : SimpleGraph V
  isTree : IsTree graph
  partA : Finset V
  partB : Finset V
  disjoint : Disjoint partA partB
  cover : partA ∪ partB = Finset.univ
  sizeA : partA.card = k
  sizeB : partB.card = 2 * k
  bipartite : ∀ u v : V, graph.Adj u v → (u ∈ partA ∧ v ∈ partB) ∨ (u ∈ partB ∧ v ∈ partA)

/-! ## Ramsey Numbers for Graphs -/

/-- An edge 2-coloring of a graph -/
def EdgeTwoColoring (V : Type*) := Sym2 V → Bool

/-- A graph H appears monochromatically in coloring c on graph G -/
def HasMonochromaticCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (c : EdgeTwoColoring V) (color : Bool) : Prop :=
  ∃ f : W → V, Function.Injective f ∧
    ∀ u v : W, H.Adj u v → G.Adj (f u) (f v) ∧ c ⟦(f u, f v)⟧ = color

/-- The Ramsey number R(H) for a graph H -/
def RamseyNumber {W : Type*} (H : SimpleGraph W) : ℕ :=
  Nat.find (ramsey_exists H)
where
  ramsey_exists (H : SimpleGraph W) : ∃ n : ℕ, ∀ c : EdgeTwoColoring (Fin n),
      HasMonochromaticCopy (completeGraph (Fin n)) H c true ∨
      HasMonochromaticCopy (completeGraph (Fin n)) H c false := by
    sorry

/-- Alternative predicate definition -/
def IsRamseyNumber {W : Type*} (H : SimpleGraph W) (n : ℕ) : Prop :=
  (∀ c : EdgeTwoColoring (Fin n),
    HasMonochromaticCopy (completeGraph (Fin n)) H c true ∨
    HasMonochromaticCopy (completeGraph (Fin n)) H c false) ∧
  (∀ m < n, ∃ c : EdgeTwoColoring (Fin m),
    ¬HasMonochromaticCopy (completeGraph (Fin m)) H c true ∧
    ¬HasMonochromaticCopy (completeGraph (Fin m)) H c false)

/-! ## Star Graphs -/

/-- The star graph S_n with n leaves (n+1 vertices total) -/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj u v := (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)
  symm := by intro u v; simp [or_comm, and_comm]
  loopless := by intro u; simp

/-- The double star: connect centers of S_k and S_{2k} -/
def doubleStar (k : ℕ) : SimpleGraph (Fin (3 * k + 2)) where
  Adj u v := by
    -- Center of first star is 0, leaves are 1..k
    -- Center of second star is k+1, leaves are k+2..3k+1
    -- Edge between centers: 0 and k+1
    exact (u = 0 ∧ (1 ≤ v.val ∧ v.val ≤ k ∨ v.val = k + 1)) ∨
          (v = 0 ∧ (1 ≤ u.val ∧ u.val ≤ k ∨ u.val = k + 1)) ∨
          (u.val = k + 1 ∧ k + 2 ≤ v.val) ∨
          (v.val = k + 1 ∧ k + 2 ≤ u.val)
  symm := by intro u v; simp [or_comm, and_comm]
  loopless := by intro u; simp; omega

/-- The double star has 3k + 2 vertices -/
theorem doubleStar_vertices (k : ℕ) : Fintype.card (Fin (3 * k + 2)) = 3 * k + 2 := by
  simp

/-! ## The Original Conjecture -/

/-- Erdős's original conjecture (now known to be FALSE) -/
def erdosConjecture549 : Prop :=
  ∀ k ≥ 1, ∀ T : BipartiteTree k,
    @RamseyNumber T.V T.graph = 4 * k - 1

/-! ## The Counterexample -/

/-- Norin-Sun-Zhao: The double star violates the conjecture -/
theorem norin_sun_zhao_counterexample : ∃ k : ℕ, k ≥ 1 ∧
    ∃ T : BipartiteTree k, @RamseyNumber T.V T.graph > 4 * k - 1 := by
  sorry

/-- More precisely: R(double star) ≥ (4.2 - o(1))k -/
theorem double_star_lower_bound : ∃ c : ℝ, c > 4 ∧
    ∀ k ≥ 1, (RamseyNumber (doubleStar k) : ℝ) ≥ c * k := by
  sorry

/-- The constant is approximately 4.2 -/
def norinSunZhaoConstant : ℝ := 4.2

theorem double_star_asymptotic :
    ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
      (RamseyNumber (doubleStar k) : ℝ) ≥ (norinSunZhaoConstant - ε) * k := by
  sorry

/-! ## Upper Bounds -/

/-- Flag algebra upper bound: R(T) ≤ (4.21526 + o(1))k -/
def flagAlgebraConstant : ℝ := 4.21526

theorem flag_algebra_upper_bound : ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
    ∀ T : BipartiteTree k,
      (@RamseyNumber T.V T.graph : ℝ) ≤ (flagAlgebraConstant + ε) * k := by
  sorry

/-- The gap between lower and upper bounds is small: 4.2 ≤ best ≤ 4.21526 -/
theorem bounds_gap : flagAlgebraConstant - norinSunZhaoConstant < 0.02 := by
  native_decide

/-! ## Special Cases Where Conjecture Holds -/

/-- The path graph P_n -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := (u.val + 1 = v.val) ∨ (v.val + 1 = u.val)
  symm := by intro u v; simp [or_comm]
  loopless := by intro u; simp; omega

/-- A broom: a path with a star at one end -/
def broomGraph (pathLen starSize : ℕ) : SimpleGraph (Fin (pathLen + starSize)) where
  Adj u v := by
    -- Path: 0 -- 1 -- ... -- (pathLen-1)
    -- Star leaves attached to vertex (pathLen-1): pathLen, ..., pathLen+starSize-1
    exact (u.val + 1 = v.val ∧ v.val < pathLen) ∨
          (v.val + 1 = u.val ∧ u.val < pathLen) ∨
          (u.val = pathLen - 1 ∧ v.val ≥ pathLen) ∨
          (v.val = pathLen - 1 ∧ u.val ≥ pathLen)
  symm := by intro u v; simp [or_comm, and_comm]
  loopless := by intro u; simp; omega

/-- Trees with bounded maximum degree satisfy the conjecture -/
theorem bounded_degree_conjecture (Δ : ℕ) : ∃ K : ℕ, ∀ k ≥ K,
    ∀ T : BipartiteTree k,
      (∀ v, T.graph.degree v ≤ Δ) →
        @RamseyNumber T.V T.graph = 4 * k - 1 := by
  sorry

/-- Brooms satisfy the original conjecture -/
theorem broom_ramsey (a b : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) :
    ∃ k : ℕ, RamseyNumber (broomGraph a b) = 4 * k - 1 := by
  sorry

/-! ## Lower Bound Construction -/

/-- The lower bound R(T) ≥ 4k - 1 always holds for bipartite (k, 2k) trees -/
theorem general_lower_bound (k : ℕ) (hk : k ≥ 1) (T : BipartiteTree k) :
    @RamseyNumber T.V T.graph ≥ 4 * k - 1 := by
  sorry

/-- Construction: K_{2k-1, 2k-1} with appropriate coloring avoids T -/
theorem lower_bound_construction (k : ℕ) (hk : k ≥ 1) (T : BipartiteTree k) :
    ∃ c : EdgeTwoColoring (Fin (4 * k - 2)),
      ¬HasMonochromaticCopy (completeGraph (Fin (4 * k - 2))) T.graph c true ∧
      ¬HasMonochromaticCopy (completeGraph (Fin (4 * k - 2))) T.graph c false := by
  sorry

/-! ## Related Results -/

/-- For any tree T on n vertices, R(T) ≤ 2n - 2 (Chvátal-Harary) -/
theorem chvatal_harary {V : Type*} [Fintype V] (T : SimpleGraph V) (hT : IsTree T) :
    RamseyNumber T ≤ 2 * Fintype.card V - 2 := by
  sorry

/-- Stars have R(S_n) = 2n - 1 -/
theorem star_ramsey (n : ℕ) (hn : n ≥ 1) :
    RamseyNumber (starGraph n) = 2 * n - 1 := by
  sorry

/-- Paths have R(P_n) = n (for n ≥ 2) -/
theorem path_ramsey (n : ℕ) (hn : n ≥ 2) :
    RamseyNumber (pathGraph n) = n := by
  sorry

/-! ## The Burr-Erdős Conjecture -/

/-- The Burr-Erdős conjecture: R(H) = (χ(H) - 1)(|H| - 1) + 1 for nice H -/
def burrErdosFormula {V : Type*} [Fintype V] (H : SimpleGraph V) (χ : ℕ) : ℕ :=
  (χ - 1) * (Fintype.card V - 1) + 1

/-- For trees, χ = 2, so the formula gives 2|T| - 1 when specialized -/
theorem tree_burr_erdos {V : Type*} [Fintype V] (T : SimpleGraph V) (hT : IsTree T) :
    burrErdosFormula T 2 = 2 * Fintype.card V - 1 := by
  simp [burrErdosFormula]
  ring

/-! ## Main Result -/

/-- Erdős Problem #549: SOLVED (Disproved)

    The conjecture R(T) = 4k - 1 for bipartite (k, 2k) trees is FALSE.

    Counterexample: The double star (S_k ∪ S_{2k} with connected centers)
    has R(double star) ≥ 4.2k > 4k - 1.

    Best bounds: 4.2k ≤ R(double star) ≤ 4.21526k -/
theorem erdos_549 : ¬erdosConjecture549 := by
  intro h
  sorry

/-- The conjecture fails for sufficiently large k -/
theorem erdos_549_counterexample : ∃ k₀ : ℕ, ∀ k ≥ k₀,
    ∃ T : BipartiteTree k, @RamseyNumber T.V T.graph ≠ 4 * k - 1 := by
  sorry

#check erdos_549
#check norin_sun_zhao_counterexample
#check double_star_lower_bound
#check flag_algebra_upper_bound
