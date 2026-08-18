import Proofs.Erdos85ExcessThreeSectorCount

/-!
# The fourth adjacency moment of a `C₄`-free graph

For every finite simple `C₄`-free graph `H`, the fourth adjacency moment is

`tr(A_H⁴) = 2 * ∑ₓ deg_H(x)² - ∑ₓ deg_H(x)`.

This is the global form of the elementary closed-walk count: a closed walk
of length four either traverses one edge twice or has a distinguished middle
vertex and two incident edges.  The `C₄`-free hypothesis says that the
off-diagonal entries of `A_H²` are zero or one.

For the triangle-free-edge graph in the odd excess-three stratum, every
degree is one or three.  If `a` vertices have degree three, the formula pins
the moment to `|V| + 14a`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem card_common_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x : V) :
    (H.neighborFinset x ∩ H.neighborFinset x).card = H.degree x := by
  rw [Finset.inter_self, H.card_neighborFinset_eq_degree]

private theorem card_common_sq_eq_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hfree : ¬ containsC4 V H) (x y : V) :
    ((H.neighborFinset x ∩ H.neighborFinset y).card : ℤ) ^ 2 =
      ((H.neighborFinset x ∩ H.neighborFinset y).card : ℤ) +
        if y = x then (H.degree x : ℤ) ^ 2 - H.degree x else 0 := by
  by_cases hyx : y = x
  · subst y
    rw [if_pos rfl, card_common_self]
    ring
  · rw [if_neg hyx]
    have hle := common_le_one_of_not_containsC4 hfree x y (Ne.symm hyx)
    interval_cases hcard : (H.neighborFinset x ∩ H.neighborFinset y).card <;>
      norm_num

/-- For a fixed initial vertex, the sum of all common-neighbor counts is the
sum of the degrees of its neighbors. -/
private theorem sum_card_common_eq_sum_neighbor_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x : V) :
    (∑ y : V, (H.neighborFinset x ∩ H.neighborFinset y).card) =
      ∑ z ∈ H.neighborFinset x, H.degree z := by
  classical
  calc
    (∑ y : V, (H.neighborFinset x ∩ H.neighborFinset y).card) =
        ∑ y : V, ∑ z ∈ H.neighborFinset x, if H.Adj y z then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
      congr 1
      ext z
      simp [SimpleGraph.mem_neighborFinset]
    _ = ∑ z ∈ H.neighborFinset x, ∑ y : V, if H.Adj y z then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ z ∈ H.neighborFinset x, H.degree z := by
      apply Finset.sum_congr rfl
      intro z _
      rw [SimpleGraph.degree, Finset.sum_boole]
      apply congrArg Finset.card
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      exact (H.adj_comm z y).symm

/-- Double-counting oriented length-two walks. -/
theorem sum_sum_card_common_eq_sum_degree_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    (∑ x : V, ∑ y : V,
      (H.neighborFinset x ∩ H.neighborFinset y).card) =
      ∑ x : V, H.degree x ^ 2 := by
  simp_rw [sum_card_common_eq_sum_neighbor_degrees H]
  calc
    (∑ x : V, ∑ z ∈ H.neighborFinset x, H.degree z) =
        ∑ x : V, ∑ z : V, if H.Adj x z then H.degree z else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_filter]
      congr 1
      ext z
      simp [SimpleGraph.mem_neighborFinset]
    _ = ∑ z : V, ∑ x : V, if H.Adj x z then H.degree z else 0 :=
      Finset.sum_comm
    _ = ∑ z : V, H.degree z ^ 2 := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← Finset.sum_filter]
      have hfilter : Finset.univ.filter (fun x : V => H.Adj x z) =
          H.neighborFinset z := by
        ext x
        simp [SimpleGraph.mem_neighborFinset, H.adj_comm]
      rw [hfilter, Finset.sum_const, H.card_neighborFinset_eq_degree]
      simp [pow_two]

/-- **Generic fourth-moment identity.** -/
theorem trace_adjMatrix_fourth_of_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hfree : ¬ containsC4 V H) :
    Matrix.trace
        ((H.adjMatrix ℤ * H.adjMatrix ℤ) *
          (H.adjMatrix ℤ * H.adjMatrix ℤ)) =
      2 * ∑ x : V, (H.degree x : ℤ) ^ 2 -
        ∑ x : V, (H.degree x : ℤ) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  have hentry : ∀ x y : V,
      (H.adjMatrix ℤ * H.adjMatrix ℤ) x y =
        ((H.neighborFinset x ∩ H.neighborFinset y).card : ℤ) :=
    adjMatrix_sq_apply_eq_card_common H
  have hexpand :
      (∑ x : V, ∑ y : V,
        (H.adjMatrix ℤ * H.adjMatrix ℤ) x y *
          (H.adjMatrix ℤ * H.adjMatrix ℤ) y x) =
      ∑ x : V, ∑ y : V,
        ((H.neighborFinset x ∩ H.neighborFinset y).card : ℤ) *
          ((H.neighborFinset y ∩ H.neighborFinset x).card : ℤ) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hentry x y, hentry y x]
  have houter :
      (∑ x : V, ((H.adjMatrix ℤ * H.adjMatrix ℤ) *
        (H.adjMatrix ℤ * H.adjMatrix ℤ)) x x) =
      ∑ x : V, ∑ y : V,
        (H.adjMatrix ℤ * H.adjMatrix ℤ) x y *
          (H.adjMatrix ℤ * H.adjMatrix ℤ) y x := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Matrix.mul_apply]
  rw [houter, hexpand]
  have hsymm : ∀ x y : V,
      (H.neighborFinset y ∩ H.neighborFinset x).card =
        (H.neighborFinset x ∩ H.neighborFinset y).card := by
    intro x y
    rw [Finset.inter_comm]
  simp_rw [hsymm]
  simp_rw [← pow_two]
  simp_rw [card_common_sq_eq_self H hfree]
  simp_rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hwalk := sum_sum_card_common_eq_sum_degree_sq H
  have hwalkZ :
      (∑ x : V, ∑ y : V,
        ((H.neighborFinset x ∩ H.neighborFinset y).card : ℤ)) =
      ∑ x : V, (H.degree x : ℤ) ^ 2 := by
    exact_mod_cast hwalk
  rw [hwalkZ]
  simp_rw [Finset.sum_sub_distrib]
  ring

/-- The triangle-free-edge graph inherits `C₄`-freeness from the original
graph. -/
theorem triangleFreeEdgeGraph_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    ¬ containsC4 V (triangleFreeEdgeGraph G) := by
  intro hC4
  apply hfree
  apply containsC4_mono (G := triangleFreeEdgeGraph G) (G' := G)
  · intro x y hxy
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  · exact hC4

/-- **Pinned fourth moment at odd excess three.**  If `a` is the number of
vertices in the degree-three triangle-free sector, then `tr(T⁴)=|V|+14a`. -/
theorem trace_triangleFreeEdgeGraph_fourth_excessThree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    let T := triangleFreeEdgeGraph G
    Matrix.trace ((T.adjMatrix ℤ * T.adjMatrix ℤ) *
        (T.adjMatrix ℤ * T.adjMatrix ℤ)) =
      (Fintype.card V : ℤ) + 14 *
        ((Finset.univ.filter fun x : V => T.degree x = 3).card : ℤ) := by
  classical
  dsimp only
  rw [trace_adjMatrix_fourth_of_not_containsC4 _
    (triangleFreeEdgeGraph_not_containsC4 G hfree)]
  let T := triangleFreeEdgeGraph G
  have hdegT : ∀ x : V, T.degree x = 1 ∨ T.degree x = 3 := by
    intro x
    rw [← T.card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    exact excessThree_triangleFreeNeighbors_card_eq_one_or_three_of_odd
      G hfree hd hodd hreg hcard x
  have hsquares : (∑ x : V, (T.degree x : ℤ) ^ 2) =
      (Fintype.card V : ℤ) + 8 *
        ((Finset.univ.filter fun x : V => T.degree x = 3).card : ℤ) := by
    calc
      (∑ x : V, (T.degree x : ℤ) ^ 2) =
          ∑ x : V, ((1 : ℤ) + if T.degree x = 3 then 8 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        rcases hdegT x with hx | hx <;> simp [hx]
      _ = (Fintype.card V : ℤ) + 8 *
          ((Finset.univ.filter fun x : V => T.degree x = 3).card : ℤ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp [mul_comm]
  have hdegrees : (∑ x : V, (T.degree x : ℤ)) =
      (Fintype.card V : ℤ) + 2 *
        ((Finset.univ.filter fun x : V => T.degree x = 3).card : ℤ) := by
    calc
      (∑ x : V, (T.degree x : ℤ)) =
          ∑ x : V, ((1 : ℤ) + if T.degree x = 3 then 2 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        rcases hdegT x with hx | hx <;> simp [hx]
      _ = (Fintype.card V : ℤ) + 2 *
          ((Finset.univ.filter fun x : V => T.degree x = 3).card : ℤ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp [mul_comm]
  rw [hsquares, hdegrees]
  ring

/-- At odd excess three the fourth moment of the triangle-free color is
already determined by the graph-facing mixed trace `tr(A D)`.  This removes
the auxiliary sector count from later spectral or service arguments. -/
theorem trace_triangleFreeEdgeGraph_fourth_eq_seven_mul_mixed_sub_six_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    let T := triangleFreeEdgeGraph G
    Matrix.trace ((T.adjMatrix ℤ * T.adjMatrix ℤ) *
        (T.adjMatrix ℤ * T.adjMatrix ℤ)) =
      7 * Matrix.trace (G.adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) -
          6 * (Fintype.card V : ℤ) := by
  dsimp only
  rw [trace_triangleFreeEdgeGraph_fourth_excessThree
      G hfree hd hodd hreg hcard,
    trace_adjMatrix_mul_secondOrderDefect_excessThree
      G hfree hd hodd hreg hcard]
  ring

end

end Erdos85
