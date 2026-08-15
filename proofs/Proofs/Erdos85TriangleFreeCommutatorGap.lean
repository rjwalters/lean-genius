import Proofs.Erdos85ColorCommutator
import Proofs.Erdos85DefectSecondMixedMoment

/-!
# Normalizing the triangle-free side of the color commutator

The independent commutator equation has triangle-free side

`tr(A²T²) - tr(T⁴)`.

Using `A² = (d-1)I + J - C - T`, the absence of triangles in `T`, and the
generic `C₄`-free fourth-moment identity, this becomes

`d * Σ deg_T - Σ deg_T² - tr(C T²)`.

At odd excess three, where `deg_T ∈ {1,3}`, it is therefore

`(d-1)|V| + (2d-8)a - tr(C T²)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The second adjacency trace is the degree sum, without a regularity
assumption. -/
theorem trace_adjMatrix_sq_eq_sum_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    Matrix.trace (H.adjMatrix ℤ * H.adjMatrix ℤ) =
      ∑ x : V, (H.degree x : ℤ) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.diag_apply]
  rw [H.adjMatrix_mul_self_apply_self]

/-- Multiplying `A²` by the all-ones matrix records the degree-square sum. -/
theorem trace_onesMatrix_mul_adjMatrix_sq_eq_sum_degree_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    Matrix.trace (FriendshipTheoremOQ01.onesMatrix V *
        (H.adjMatrix ℤ * H.adjMatrix ℤ)) =
      ∑ x : V, (H.degree x : ℤ) ^ 2 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  have hentry : ∀ x y : V,
      (H.adjMatrix ℤ * H.adjMatrix ℤ) x y =
        ((H.neighborFinset x ∩ H.neighborFinset y).card : ℤ) :=
    adjMatrix_sq_apply_eq_card_common H
  have houter :
      (∑ x : V, (FriendshipTheoremOQ01.onesMatrix V *
        (H.adjMatrix ℤ * H.adjMatrix ℤ)) x x) =
      ∑ x : V, ∑ y : V,
        ((H.neighborFinset y ∩ H.neighborFinset x).card : ℤ) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro y _
    rw [FriendshipTheoremOQ01.onesMatrix,
      Matrix.of_apply, one_mul, hentry y x]
  rw [houter]
  have hsymm : ∀ x y : V,
      (H.neighborFinset y ∩ H.neighborFinset x).card =
        (H.neighborFinset x ∩ H.neighborFinset y).card := by
    intro x y
    rw [Finset.inter_comm]
  simp_rw [hsymm]
  have hwalk := sum_sum_card_common_eq_sum_degree_sq H
  exact_mod_cast hwalk

/-- The triangle-free-edge color has no triangles. -/
theorem trace_triangleFreeEdgeGraph_cube_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    Matrix.trace (T * T * T) = 0 := by
  dsimp only
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro x _
  change ((triangleFreeEdgeGraph G).adjMatrix ℤ *
    (triangleFreeEdgeGraph G).adjMatrix ℤ *
    (triangleFreeEdgeGraph G).adjMatrix ℤ) x x = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hzx : (triangleFreeEdgeGraph G).Adj z x
  · rw [SimpleGraph.adjMatrix_apply, if_pos hzx, mul_one]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hxy : (triangleFreeEdgeGraph G).Adj x y
    · by_cases hyz : (triangleFreeEdgeGraph G).Adj y z
      · have hGxy : G.Adj x y :=
          ((mem_triangleFreeNeighbors G x y).mp hxy).1
        exact (false_of_adj_two_triangleFree_triangle G hGxy hyz hzx).elim
      · have hz : (triangleFreeEdgeGraph G).adjMatrix ℤ y z = 0 := by
          rw [SimpleGraph.adjMatrix_apply, if_neg hyz]
        rw [hz, mul_zero]
    · have hx : (triangleFreeEdgeGraph G).adjMatrix ℤ x y = 0 := by
        rw [SimpleGraph.adjMatrix_apply, if_neg hxy]
      rw [hx, zero_mul]
  · have hz : (triangleFreeEdgeGraph G).adjMatrix ℤ z x = 0 := by
      rw [SimpleGraph.adjMatrix_apply, if_neg hzx]
    rw [hz, mul_zero]

/-- An antipodal pair cannot be closed by two triangle-free original edges,
because their middle vertex would be a common original neighbor. -/
theorem false_of_antipodal_two_triangleFree_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y z : V} (hxy : (antipodalGraph G).Adj x y)
    (hyz : (triangleFreeEdgeGraph G).Adj y z)
    (hzx : (triangleFreeEdgeGraph G).Adj z x) : False := by
  have hzero : G.neighborFinset x ∩ G.neighborFinset y = ∅ :=
    Finset.card_eq_zero.mp
      ((mem_antipodalNeighbors G x y).mp
        ((antipodalGraph_adj G x y).mp hxy)).2.2
  have hxz : G.Adj x z :=
    ((mem_triangleFreeNeighbors G z x).mp hzx).1.symm
  have hyzG : G.Adj y z :=
    ((mem_triangleFreeNeighbors G y z).mp hyz).1
  have hzmem : z ∈ G.neighborFinset x ∩ G.neighborFinset y := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxz, hyzG⟩
  rw [hzero] at hzmem
  exact Finset.notMem_empty z hzmem

/-- The mixed color triangle `C T²` is absent at every excess. -/
theorem trace_antipodal_mul_triangleFree_sq_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    let C := (antipodalGraph G).adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    Matrix.trace (C * (T * T)) = 0 := by
  dsimp only
  rw [← Matrix.mul_assoc, Matrix.trace]
  apply Finset.sum_eq_zero
  intro x _
  change ((antipodalGraph G).adjMatrix ℤ *
    (triangleFreeEdgeGraph G).adjMatrix ℤ *
    (triangleFreeEdgeGraph G).adjMatrix ℤ) x x = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hzx : (triangleFreeEdgeGraph G).Adj z x
  · rw [SimpleGraph.adjMatrix_apply, if_pos hzx, mul_one]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hxy : (antipodalGraph G).Adj x y
    · by_cases hyz : (triangleFreeEdgeGraph G).Adj y z
      · exact (false_of_antipodal_two_triangleFree_triangle
          G hxy hyz hzx).elim
      · have hz : (triangleFreeEdgeGraph G).adjMatrix ℤ y z = 0 := by
          rw [SimpleGraph.adjMatrix_apply, if_neg hyz]
        rw [hz, mul_zero]
    · have hx : (antipodalGraph G).adjMatrix ℤ x y = 0 := by
        rw [SimpleGraph.adjMatrix_apply, if_neg hxy]
      rw [hx, zero_mul]
  · have hz : (triangleFreeEdgeGraph G).adjMatrix ℤ z x = 0 := by
      rw [SimpleGraph.adjMatrix_apply, if_neg hzx]
    rw [hz, mul_zero]

/-- The triangle-free side of the commutator gap in degree-moment form. -/
theorem trace_adj_sq_triangleFree_sq_sub_fourth_eq_degreeMoments_sub_mixed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    Matrix.trace ((A * A) * (T * T)) -
        Matrix.trace ((T * T) * (T * T)) =
      (d : ℤ) * (∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ)) -
        (∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ) ^ 2) -
          Matrix.trace (C * (T * T)) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hsq : A * A = (↑d - 1 : ℤ) • (1 : Matrix V V ℤ) + J - (C + T) := by
    have h := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
    rw [secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G] at h
    exact h
  have hT2 := trace_adjMatrix_sq_eq_sum_degrees (triangleFreeEdgeGraph G)
  change Matrix.trace (T * T) = _ at hT2
  have hJT2 := trace_onesMatrix_mul_adjMatrix_sq_eq_sum_degree_sq
    (triangleFreeEdgeGraph G)
  change Matrix.trace (J * (T * T)) = _ at hJT2
  have hT3 := trace_triangleFreeEdgeGraph_cube_eq_zero G
  change Matrix.trace (T * T * T) = 0 at hT3
  have hT3' : Matrix.trace (T * (T * T)) = 0 := by
    rw [← Matrix.mul_assoc]
    exact hT3
  have hT4 := trace_adjMatrix_fourth_of_not_containsC4
    (triangleFreeEdgeGraph G) (triangleFreeEdgeGraph_not_containsC4 G hfree)
  change Matrix.trace ((T * T) * (T * T)) = _ at hT4
  rw [hsq, sub_mul, add_mul, add_mul, smul_mul_assoc, Matrix.one_mul,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_smul, hT2, hJT2, hT3', hT4]
  ring

/-- With the forbidden `C T²` triangle removed, the triangle-free
commutator gap depends only on its first two degree moments. -/
theorem trace_adj_sq_triangleFree_sq_sub_fourth_eq_degreeMoments
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    let A := G.adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    Matrix.trace ((A * A) * (T * T)) -
        Matrix.trace ((T * T) * (T * T)) =
      (d : ℤ) * (∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ)) -
        (∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ) ^ 2) := by
  dsimp only
  rw [trace_adj_sq_triangleFree_sq_sub_fourth_eq_degreeMoments_sub_mixed
      G hfree hreg,
    trace_antipodal_mul_triangleFree_sq_eq_zero G, sub_zero]

/-- The fourth-word triangle-free commutator gap at even excess two is an
explicit linear form in the two nonzero color-sector sizes. -/
theorem trace_triangleFree_commutatorGap_even_excessTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 5) :
    let A := G.adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let s2 := (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2).card
    let s4 := (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 4).card
    Matrix.trace ((A * A) * (T * T)) -
        Matrix.trace ((T * T) * (T * T)) =
      (2 * (d : ℤ) - 4) * (s2 : ℤ) +
        (4 * (d : ℤ) - 16) * (s4 : ℤ) := by
  dsimp only
  let Tgraph := triangleFreeEdgeGraph G
  let s2 := (Finset.univ.filter fun x : V => Tgraph.degree x = 2).card
  let s4 := (Finset.univ.filter fun x : V => Tgraph.degree x = 4).card
  have hsum1 : (∑ x : V, (Tgraph.degree x : ℤ)) =
      2 * (s2 : ℤ) + 4 * (s4 : ℤ) := by
    have h := trace_adjMatrix_mul_secondOrderDefect_even_excessTwo
      G hfree heven hreg hcard
    rw [trace_adjMatrix_mul_secondOrderDefect_eq_sum_triangleFreeDegrees] at h
    exact h
  have hsum2 : (∑ x : V, (Tgraph.degree x : ℤ) ^ 2) =
      4 * (s2 : ℤ) + 16 * (s4 : ℤ) := by
    calc
      (∑ x : V, (Tgraph.degree x : ℤ) ^ 2) =
          ∑ x : V, (4 * (if Tgraph.degree x = 2 then 1 else 0) +
            16 * (if Tgraph.degree x = 4 then 1 else 0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rcases excessTwo_even_color_degree_classification
            G hfree heven hreg hcard x with hx | hx | hx
        · simp [Tgraph, hx.1]
        · simp [Tgraph, hx.1]
        · simp [Tgraph, hx.1]
      _ = 4 * (s2 : ℤ) + 16 * (s4 : ℤ) := by
        dsimp [s2, s4]
        rw [Finset.sum_add_distrib]
        simp only [mul_ite, mul_one, mul_zero]
        rw [← Finset.sum_filter, ← Finset.sum_filter]
        simp [mul_comm]
  rw [trace_adj_sq_triangleFree_sq_sub_fourth_eq_degreeMoments
      G hfree hreg, hsum1, hsum2]
  ring

/-- At order 35 and degree six, the fourth-word gap is eight times the
number of vertices in a nonzero triangle-free color sector. -/
theorem degreeSix_thirtyFive_triangleFree_commutatorGap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hcard : Fintype.card V = 35) :
    let A := G.adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    Matrix.trace ((A * A) * (T * T)) -
        Matrix.trace ((T * T) * (T * T)) =
      8 * (((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) +
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 4).card : ℤ)) := by
  have h := trace_triangleFree_commutatorGap_even_excessTwo
    G hfree (d := 6) (by norm_num) hreg (by omega)
  dsimp only at h ⊢
  norm_num at h
  rw [mul_add]
  exact h

/-- Equivalent antipodal fourth-word form of the order-35 gap. -/
theorem degreeSix_thirtyFive_antipodal_commutatorGap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hcard : Fintype.card V = 35) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    Matrix.trace ((A * A) * (C * C)) -
        Matrix.trace ((A * C) * (A * C)) =
      8 * (((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) +
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 4).card : ℤ)) := by
  dsimp only
  rw [trace_adj_sq_antipodal_sq_sub_alternating_eq_triangleFree_gap
      G hfree hreg,
    degreeSix_thirtyFive_triangleFree_commutatorGap G hfree hreg hcard]

/-- Frobenius form: the triangle-free color commutator has squared trace
`-16` times the number of vertices in a nonzero color sector. -/
theorem degreeSix_thirtyFive_triangleFree_commutator_sq_trace
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hcard : Fintype.card V = 35) :
    let A := G.adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    Matrix.trace ((A * T - T * A) * (A * T - T * A)) =
      -16 * (((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) +
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 4).card : ℤ)) := by
  dsimp only
  rw [trace_commutator_sq_eq_two_mul_alternating_sub_square]
  have hTle : triangleFreeEdgeGraph G ≤ G := by
    intro x y hxy
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  have halt := trace_adj_subgraph_adj_subgraph_eq_trace_subgraph_fourth
    G (triangleFreeEdgeGraph G) hfree hTle
  change Matrix.trace ((G.adjMatrix ℤ *
      (triangleFreeEdgeGraph G).adjMatrix ℤ) *
        (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ)) =
    Matrix.trace (((triangleFreeEdgeGraph G).adjMatrix ℤ *
      (triangleFreeEdgeGraph G).adjMatrix ℤ) *
        ((triangleFreeEdgeGraph G).adjMatrix ℤ *
          (triangleFreeEdgeGraph G).adjMatrix ℤ)) at halt
  rw [halt]
  have hgap := degreeSix_thirtyFive_triangleFree_commutatorGap
    G hfree hreg hcard
  dsimp only at hgap
  linear_combination -2 * hgap

/-- The negative trace of the square of a skew-symmetric integer matrix is
its entrywise squared norm. -/
theorem neg_trace_sq_eq_sum_entry_sq_of_skew
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℤ)
    (hskew : ∀ i j, K j i = -K i j) :
    -Matrix.trace (K * K) = ∑ i : ι, ∑ j : ι, (K i j) ^ 2 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  calc
    -(∑ i, ∑ j, K i j * K j i) =
        ∑ i, -(∑ j, K i j * K j i) := by simp
    _ = ∑ i, ∑ j, -(K i j * K j i) := by simp
    _ = ∑ i, ∑ j, (K i j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hskew i j]
      ring

/-- The commutator of two symmetric integer matrices is skew-symmetric. -/
theorem matrix_commutator_apply_swap_eq_neg
    {ι : Type*} [Fintype ι]
    (A T : Matrix ι ι ℤ)
    (hA : ∀ i j, A j i = A i j)
    (hT : ∀ i j, T j i = T i j) :
    ∀ i j, (A * T - T * A) j i = -(A * T - T * A) i j := by
  intro i j
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  have hAT : (∑ k, A j k * T k i) = ∑ k, T i k * A k j := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hA j k, hT k i, mul_comm]
  have hTA : (∑ k, T j k * A k i) = ∑ k, A i k * T k j := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hT j k, hA k i, mul_comm]
  rw [hAT, hTA]
  ring

/-- Entrywise Frobenius form of the order-35 color commutator identity. -/
theorem degreeSix_thirtyFive_triangleFree_commutator_entry_sq_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hcard : Fintype.card V = 35) :
    let A := G.adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    (∑ i : V, ∑ j : V, ((A * T - T * A) i j) ^ 2) =
      16 * (((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) +
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 4).card : ℤ)) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  have hA : ∀ i j, A j i = A i j := by
    intro i j
    simp only [A, SimpleGraph.adjMatrix_apply]
    simp [G.adj_comm]
  have hT : ∀ i j, T j i = T i j := by
    intro i j
    simp only [T, SimpleGraph.adjMatrix_apply]
    by_cases hij : G.Adj i j
    · have hji : G.Adj j i := (G.adj_comm i j).mp hij
      by_cases hempty : G.neighborFinset i ∩ G.neighborFinset j = ∅
      · have hempty' : G.neighborFinset j ∩ G.neighborFinset i = ∅ := by
          simpa [Finset.inter_comm] using hempty
        simp [hij, hji, hempty, hempty']
      · have hempty' : G.neighborFinset j ∩ G.neighborFinset i ≠ ∅ := by
          simpa [Finset.inter_comm] using hempty
        simp [hij, hji, hempty, hempty']
    · have hji : ¬G.Adj j i := by
        intro hji
        exact hij ((G.adj_comm j i).mp hji)
      simp [hij, hji]
  have hnorm := neg_trace_sq_eq_sum_entry_sq_of_skew
    (A * T - T * A) (matrix_commutator_apply_swap_eq_neg A T hA hT)
  have htrace := degreeSix_thirtyFive_triangleFree_commutator_sq_trace
    G hfree hreg hcard
  dsimp only at htrace
  change Matrix.trace ((A * T - T * A) * (A * T - T * A)) = _ at htrace
  rw [htrace] at hnorm
  rw [← hnorm]
  ring

/-- **Odd excess-three normalization.**  The whole triangle-free side is a
known affine expression in the degree-three sector size, apart from the
single mixed count `tr(C T²)`. -/
theorem trace_adj_sq_triangleFree_sq_sub_fourth_excessThree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    let A := G.adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let a := (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 3).card
    Matrix.trace ((A * A) * (T * T)) -
        Matrix.trace ((T * T) * (T * T)) =
      (d - 1 : ℤ) * (Fintype.card V : ℤ) +
        (2 * (d : ℤ) - 8) * (a : ℤ) := by
  dsimp only
  let Tgraph := triangleFreeEdgeGraph G
  let a := (Finset.univ.filter fun x : V => Tgraph.degree x = 3).card
  have hsum1 : (∑ x : V, (Tgraph.degree x : ℤ)) =
      (Fintype.card V : ℤ) + 2 * (a : ℤ) := by
    have h := trace_adjMatrix_mul_secondOrderDefect_excessThree
      G hfree hd hodd hreg hcard
    rw [trace_adjMatrix_mul_secondOrderDefect_eq_sum_triangleFreeDegrees] at h
    exact h
  have hsum2 : (∑ x : V, (Tgraph.degree x : ℤ) ^ 2) =
      (Fintype.card V : ℤ) + 8 * (a : ℤ) := by
    have hdegT : ∀ x : V, Tgraph.degree x = 1 ∨ Tgraph.degree x = 3 := by
      intro x
      rw [← Tgraph.card_neighborFinset_eq_degree,
        triangleFreeEdgeGraph_neighborFinset]
      exact excessThree_triangleFreeNeighbors_card_eq_one_or_three_of_odd
        G hfree hd hodd hreg hcard x
    calc
      (∑ x : V, (Tgraph.degree x : ℤ) ^ 2) =
          ∑ x : V, ((1 : ℤ) + if Tgraph.degree x = 3 then 8 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        rcases hdegT x with hx | hx <;> simp [hx]
      _ = (Fintype.card V : ℤ) + 8 * (a : ℤ) := by
        dsimp [a]
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp [mul_comm]
  rw [trace_adj_sq_triangleFree_sq_sub_fourth_eq_degreeMoments
      G hfree hreg, hsum1, hsum2]
  ring

/-- **Pinned antipodal commutator gap at odd excess three.**  Combining the
color-commutator equation with the preceding normalization determines the
previously unknown antipodal fourth-word difference exactly. -/
theorem trace_adj_sq_antipodal_sq_sub_alternating_excessThree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let a := (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 3).card
    Matrix.trace ((A * A) * (C * C)) -
        Matrix.trace ((A * C) * (A * C)) =
      (d - 1 : ℤ) * (Fintype.card V : ℤ) +
        (2 * (d : ℤ) - 8) * (a : ℤ) := by
  dsimp only
  rw [trace_adj_sq_antipodal_sq_sub_alternating_eq_triangleFree_gap
      G hfree hreg,
    trace_adj_sq_triangleFree_sq_sub_fourth_excessThree
      G hfree hd hodd hreg hcard]

end

end Erdos85
