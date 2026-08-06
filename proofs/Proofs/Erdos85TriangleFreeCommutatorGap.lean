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
    let C := (antipodalGraph G).adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let a := (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 3).card
    Matrix.trace ((A * A) * (T * T)) -
        Matrix.trace ((T * T) * (T * T)) =
      (d - 1 : ℤ) * (Fintype.card V : ℤ) +
        (2 * (d : ℤ) - 8) * (a : ℤ) -
          Matrix.trace (C * (T * T)) := by
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
  rw [trace_adj_sq_triangleFree_sq_sub_fourth_eq_degreeMoments_sub_mixed
      G hfree hreg, hsum1, hsum2]
  ring

end

end Erdos85
