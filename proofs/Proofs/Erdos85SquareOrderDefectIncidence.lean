import Proofs.Erdos85SquareOrderSectorProfile
import Proofs.Erdos85NonregularDefectOperator
import Proofs.Erdos85BranchDeficitSymmetry

/-!
# High incidence coupled to the defect graph at square order

The high-count moments alone leave many arithmetically feasible profiles.  The
nonregular adjacency/defect commutator supplies the missing pointwise coupling:
if `k(y)` counts high neighbors of a low vertex and `D` is the second-order
defect graph, then `(D + I) k = h 1`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If `x` is high and `y` is low, precisely one neighbor of `x` is a defect
neighbor of `y` when `x,y` are nonadjacent, and none is when they are
adjacent.  This is the uniform square-order identity `B (D + I) = J`. -/
theorem squareOrder_card_highNeighbors_inter_defectNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ z : V, d ≤ G.degree z)
    (hcard : Fintype.card V = d * d) {x y : V}
    (hx : G.degree x = d + 1) (hy : G.degree y = d) :
    (G.neighborFinset x ∩
        (secondOrderDefectGraph G).neighborFinset y).card =
      if G.Adj x y then 0 else 1 := by
  let D := secondOrderDefectGraph G
  have hxD : D.degree x = 0 :=
    (squareOrder_degree_succ_highRoot_structure
      G hfree hd hmin hcard hx).1
  have hxDempty : D.neighborFinset x = ∅ := by
    rw [← Finset.card_eq_zero, D.card_neighborFinset_eq_degree, hxD]
  have hcomm := adjMatrix_secondOrderDefect_commutator_apply G hfree x y
  rw [Matrix.sub_apply,
    adjMatrix_mul_subgraph_apply_eq_card_mixed G D x y,
    adjMatrix_mul_subgraph_apply_eq_card_mixed D G x y,
    hxDempty] at hcomm
  simp only [Finset.empty_inter, Finset.card_empty, Int.ofNat_zero, sub_zero,
    hx, hy, SimpleGraph.adjMatrix_apply] at hcomm
  by_cases hxy : G.Adj x y
  · rw [if_pos hxy]
    simp [hxy] at hcomm
    exact Finset.card_eq_zero.mpr hcomm
  · rw [if_neg hxy]
    simp [hxy] at hcomm
    omega

/-- Pointwise weighted defect identity.  For every low vertex `y`, its high
incidence plus the total high incidence of its defect neighbors is the total
number `h` of high vertices: `(D + I) k = h 1`. -/
theorem squareOrder_sum_highIncidence_over_defectNeighbors_add_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ z : V, d ≤ G.degree z)
    (hcard : Fintype.card V = d * d) {y : V}
    (hy : G.degree y = d) :
    (∑ x ∈ (secondOrderDefectGraph G).neighborFinset y,
        squareOrderHighIncidenceCount G d x) +
      squareOrderHighIncidenceCount G d y =
        (squareOrderHighVertices G d).card := by
  let D := secondOrderDefectGraph G
  let H := squareOrderHighVertices G d
  have hswap := sum_card_neighbor_inter_comm G (D.neighborFinset y) H
  have hterm : ∀ v ∈ H,
      (G.neighborFinset v ∩ D.neighborFinset y).card =
        if G.Adj v y then 0 else 1 := by
    intro v hv
    have hvHigh : G.degree v = d + 1 := (Finset.mem_filter.mp hv).2
    exact squareOrder_card_highNeighbors_inter_defectNeighbors
      G hfree hd hmin hcard hvHigh hy
  have hsum :
      (∑ x ∈ D.neighborFinset y,
          (G.neighborFinset x ∩ H).card) =
        (H \ G.neighborFinset y).card := by
    rw [hswap]
    calc
      (∑ v ∈ H, (G.neighborFinset v ∩ D.neighborFinset y).card) =
          ∑ v ∈ H, if G.Adj v y then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hterm v hv
      _ = (H \ G.neighborFinset y).card := by
        have hbool : ∀ v : V,
            (if G.Adj v y then 0 else 1) =
              (if ¬ G.Adj y v then 1 else 0) := by
          intro v
          by_cases hvy : G.Adj v y
          · have hyv : G.Adj y v := by simpa [G.adj_comm] using hvy
            simp [hvy, hyv]
          · have hyv : ¬ G.Adj y v := by simpa [G.adj_comm] using hvy
            simp [hvy, hyv]
        simp_rw [hbool]
        rw [Finset.sum_boole]
        apply congrArg Finset.card
        ext v
        simp [SimpleGraph.mem_neighborFinset]
  change
    (∑ x ∈ D.neighborFinset y, (G.neighborFinset x ∩ H).card) +
      (G.neighborFinset y ∩ H).card = H.card
  rw [hsum, Finset.card_sdiff]
  exact Nat.sub_add_cancel (Finset.card_le_card Finset.inter_subset_right)

/-- At square order, neighbor degree excess is exactly the number of high
neighbors. -/
theorem squareOrder_neighborDegreeExcess_eq_highIncidenceCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ z : V, d ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) (x : V) :
    neighborDegreeExcess G d x = squareOrderHighIncidenceCount G d x := by
  rw [neighborDegreeExcess_eq_sum_neighborFinset]
  have hterm : ∀ y ∈ G.neighborFinset x,
      G.degree y - d = if G.degree y = d + 1 then 1 else 0 := by
    intro y _hy
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree hd hmin hcover hcard y with hyLow | hyHigh
    · simp [hyLow]
    · simp [hyHigh]
  calc
    (∑ y ∈ G.neighborFinset x, (G.degree y - d)) =
        ∑ y ∈ G.neighborFinset x,
          if G.degree y = d + 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hterm y hy
    _ = ((G.neighborFinset x).filter
          fun y => G.degree y = d + 1).card := by
      rw [Finset.card_filter]
    _ = squareOrderHighIncidenceCount G d x := by
      unfold squareOrderHighIncidenceCount
      congr 1
      ext y
      simp [squareOrderHighVertices, and_comm]

/-- A low vertex of high incidence `k(y)` has defect degree `d-1-k(y)`.
Equivalently, `deg_D(y) + k(y) = d-1`. -/
theorem squareOrder_defectDegree_add_highIncidence_eq_pred
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ z : V, d ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) {x : V}
    (hx : G.degree x = d) :
    (secondOrderDefectGraph G).degree x +
      squareOrderHighIncidenceCount G d x = d - 1 := by
  have hcard' : Fintype.card V = d * (d - 1) + 1 + (d - 1) := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 :=
      ⟨d - 2, (Nat.sub_add_cancel hd).symm⟩
    norm_num
    ring
  have hbudget :=
    secondOrderDefect_degree_add_weightedExcess_add_neighborExcess
      G hfree (d := d) (q := d - 1) (by omega) hmin hcard' x
  rw [hx, Nat.sub_self, zero_mul, Nat.add_zero,
    squareOrder_neighborDegreeExcess_eq_highIncidenceCount
      G hfree hd hmin hcover hcard x] at hbudget
  exact hbudget

end

end Erdos85
