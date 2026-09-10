import Proofs.Erdos85OrderFortyNineLocalEdgePartition
import Proofs.Erdos85OrderFortyNineHighIncidenceCensus
import Proofs.Erdos85RootedFifthWalkDefectNeighborhood

/-! Cubic trace in terms of the existing all-low local triangle incidence
sum. This avoids introducing a second representation of triangle objects. -/
namespace Erdos85
open SimpleGraph Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A high root has four edges in its neighborhood. -/
theorem orderFortyNine_localEdges_eq_four_of_high
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 8) :
    (G.induce (G.neighborSet x)).edgeFinset.card = 4 := by
  have hh := (G.induce (G.neighborSet x)).sum_degrees_eq_twice_card_edges
  have hs : (∑ y : G.neighborSet x, (G.induce (G.neighborSet x)).degree y) = 8 := by
    calc
      _ = ∑ _y : G.neighborSet x, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro y _
        exact orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight G hfree hmin hcard hx y
      _ = 8 := by simp [G.card_neighborSet_eq_degree, hx]
  omega

/-- The complete adjacency cubic trace is twice all-low triangle incidence
plus twenty-four times the number of high vertices. -/
theorem orderFortyNine_cubic_trace_eq_lowLow_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    Matrix.trace (G.adjMatrix ℤ ^ 3) =
      2 * (∑ x ∈ orderFortyNineLowVertices G,
        (orderFortyNineLowLowLocalEdgeCount G x : ℤ)) +
      24 * ((orderFortyNineHighVertices G).card : ℤ) := by
  classical
  let H := orderFortyNineHighVertices G
  let L := orderFortyNineLowVertices G
  let t := fun x => (G.neighborFinset x ∩ H).card
  let e := fun x => (G.induce (G.neighborSet x)).edgeFinset.card
  have split_sum (f : V → ℕ) : (∑ x : V, f x) = (∑ x ∈ H, f x) + ∑ x ∈ L, f x := by
    have hs := Finset.sum_sdiff (f := f) (Finset.subset_univ H)
    simpa only [orderFortyNineLowVertices, L, H, Nat.add_comm] using hs.symm
  have htH : ∑ x ∈ H, t x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx8 : G.degree x = 8 := (Finset.mem_filter.mp hx).2
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨hyN, hyH⟩ := Finset.mem_inter.mp hy
    exact orderFortyNine_not_adj_degreeEight_degreeEight G hfree hmin hcard hx8
      (Finset.mem_filter.mp hyH).2 ((G.mem_neighborFinset x y).mp hyN)
  have htL : ∑ x ∈ L, t x = 8 * H.card := by
    have hs := split_sum t
    have hall := orderFortyNine_sum_highNeighborCount_eq G
    change (∑ x : V, t x) = 8 * H.card at hall
    omega
  have heH : ∑ x ∈ H, e x = 4 * H.card := by
    calc
      _ = ∑ _x ∈ H, (4 : ℕ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact orderFortyNine_localEdges_eq_four_of_high G hfree hmin hcard (Finset.mem_filter.mp hx).2
      _ = _ := by simp [Nat.mul_comm]
  have heL : ∑ x ∈ L, e x = ∑ x ∈ L, t x + ∑ x ∈ L, orderFortyNineLowLowLocalEdgeCount G x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hx7 : G.degree x = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin hcard x with h | h
      · exact h
      · exact ((Finset.mem_sdiff.mp hx).2 (by simp [orderFortyNineHighVertices, h])).elim
    exact (orderFortyNine_high_add_lowLow_eq_localTriangleEdges G hfree hmin hcard hx7).symm
  have heall : ∑ x : V, e x = 12 * H.card + ∑ x ∈ L, orderFortyNineLowLowLocalEdgeCount G x := by
    rw [split_sum e, heH, heL, htL]
    omega
  have hcubic : Matrix.trace (G.adjMatrix ℤ ^ 3) = 2 * ∑ x : V, (e x : ℤ) := by
    rw [pow_succ, pow_two, Matrix.trace, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    let iso : G.induce (↑(G.neighborFinset x) : Set V) ≃g G.induce (G.neighborSet x) :=
      { toFun := fun y => ⟨y.1, by simpa using y.2⟩
        invFun := fun y => ⟨y.1, by simpa using y.2⟩
        left_inv := by intro y; rfl
        right_inv := by intro y; rfl
        map_rel_iff' := by intro y z; rfl }
    have hecards := iso.card_edgeFinset_eq
    have hh := defect_adj_defect_diagonal_eq_two_mul_induced_edges G G x
    rw [hecards] at hh
    exact hh
  have heint : (∑ x : V, (e x : ℤ)) =
      12 * (H.card : ℤ) + ∑ x ∈ L, (orderFortyNineLowLowLocalEdgeCount G x : ℤ) := by
    exact_mod_cast heall
  rw [hcubic, heint]
  dsimp [H, L]
  ring
end Erdos85
