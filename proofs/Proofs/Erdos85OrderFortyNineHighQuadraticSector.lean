import Proofs.Erdos85OrderFortyNineDefectEigenvectors
import Proofs.Erdos85OrderFortyNineLowNeighborhoodPartition

/-!
# The quadratic high-incidence sector at order 49

Differences of adjacency rows at degree-eight vertices generate a canonical
sector on which the square of the full adjacency operator is multiplication
by seven.  In block notation, if `X` is low--high incidence and `B` is the
low-induced adjacency matrix, the underlying identities are
`Xᵀ X = 7 I + J` and `B X = J`.

The pointwise formulation below avoids choosing an ordering of the high and
low vertices.  It is also the spectral explanation for much of the finite
high-support rigidity used in the order-49 terminal.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Multiplying a high-row difference by the full adjacency matrix produces
seven times the difference of the two coordinate vectors. -/
theorem orderFortyNine_adj_mulVec_highRowDifference
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x z : V}
    (hx : G.degree x = 8) (hz : G.degree z = 8) (hxz : x ≠ z) :
    (G.adjMatrix ℤ).mulVec (orderFortyNineHighRowDifference G x z) =
      fun y => 7 * ((if y = x then 1 else 0) - (if y = z then 1 else 0)) := by
  funext y
  change (G.adjMatrix ℤ).mulVec
      (fun w => G.adjMatrix ℤ x w - G.adjMatrix ℤ z w) y = _
  have hxm := adjMatrix_mulVec_adjRow_eq_card_mixed G G x y
  have hzm := adjMatrix_mulVec_adjRow_eq_card_mixed G G z y
  simp only [Matrix.mulVec, dotProduct] at hxm hzm ⊢
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hxm, hzm]
  by_cases hyx : y = x
  · subst y
    have hcommon := orderFortyNine_card_common_degreeEight_eq_one
      G hfree hmin hcard hx hz hxz
    have hcommon' : (G.neighborFinset z ∩ G.neighborFinset x).card = 1 := by
      simpa [Finset.inter_comm] using hcommon
    rw [show (G.neighborFinset x ∩ G.neighborFinset x).card = 8 by
      simp [G.card_neighborFinset_eq_degree, hx], hcommon']
    simp [hxz]
  · by_cases hyz : y = z
    · subst y
      have hcommon := orderFortyNine_card_common_degreeEight_eq_one
        G hfree hmin hcard hx hz hxz
      rw [hcommon, show (G.neighborFinset z ∩ G.neighborFinset z).card = 8 by
        simp [G.card_neighborFinset_eq_degree, hz]]
      simp [hyx]
    · rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard y with hy | hy
      · have hxycard : (G.neighborFinset x ∩ G.neighborFinset y).card = 1 := by
          simpa [Finset.inter_comm] using
            orderFortyNine_low_high_card_common_eq_one
              G hfree hmin hcard hy hx
        have hzycard : (G.neighborFinset z ∩ G.neighborFinset y).card = 1 := by
          simpa [Finset.inter_comm] using
            orderFortyNine_low_high_card_common_eq_one
              G hfree hmin hcard hy hz
        rw [hxycard, hzycard]
        simp [hyx, hyz]
      · have hxy : x ≠ y := Ne.symm hyx
        have hzy : z ≠ y := Ne.symm hyz
        rw [orderFortyNine_card_common_degreeEight_eq_one
              G hfree hmin hcard hx hy hxy,
            orderFortyNine_card_common_degreeEight_eq_one
              G hfree hmin hcard hz hy hzy]
        simp [hyx, hyz]

/-- Every high-row difference belongs to the square-seven sector of the
full graph adjacency operator. -/
theorem orderFortyNine_adj_sq_mulVec_highRowDifference
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x z : V}
    (hx : G.degree x = 8) (hz : G.degree z = 8) (hxz : x ≠ z) :
    (G.adjMatrix ℤ).mulVec
        ((G.adjMatrix ℤ).mulVec (orderFortyNineHighRowDifference G x z)) =
      7 • orderFortyNineHighRowDifference G x z := by
  rw [orderFortyNine_adj_mulVec_highRowDifference
    G hfree hmin hcard hx hz hxz]
  funext y
  change (∑ w, G.adjMatrix ℤ y w *
      (7 * ((if w = x then 1 else 0) - (if w = z then 1 else 0)))) =
    7 * (G.adjMatrix ℤ x y - G.adjMatrix ℤ z y)
  have hrowx : (∑ w, G.adjMatrix ℤ y w * (if w = x then 1 else 0)) =
      G.adjMatrix ℤ x y := by
    rw [Finset.sum_eq_single x]
    · simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
    · intro b _ hbx
      simp [hbx]
    · simp
  have hrowz : (∑ w, G.adjMatrix ℤ y w * (if w = z then 1 else 0)) =
      G.adjMatrix ℤ z y := by
    rw [Finset.sum_eq_single z]
    · simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
    · intro b _ hbz
      simp [hbz]
    · simp
  calc
    (∑ w, G.adjMatrix ℤ y w *
        (7 * ((if w = x then 1 else 0) - (if w = z then 1 else 0)))) =
        7 * ∑ w, (G.adjMatrix ℤ y w * (if w = x then 1 else 0) -
          G.adjMatrix ℤ y w * (if w = z then 1 else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = 7 * ((∑ w, G.adjMatrix ℤ y w * (if w = x then 1 else 0)) -
        ∑ w, G.adjMatrix ℤ y w * (if w = z then 1 else 0)) := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by rw [hrowx, hrowz]

end

end Erdos85
