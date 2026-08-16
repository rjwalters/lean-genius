import Proofs.Erdos85SquareOrderCommutatorRowCount

/-!
# Frobenius count for the square-order commutator

Summing the exact row counts shows that the two orientations of every
high--low nonedge contribute equally. Thus the squared Frobenius norm of
the adjacency/defect commutator has a closed form.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem squareOrder_sum_commutator_entry_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    let H := squareOrderHighVertices G d
    let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
    (∑ x : V, ∑ y : V, C x y * C x y) =
      2 * (H.card : ℤ) * ((d * d - H.card - (d + 1) : Nat) : ℤ) := by
  classical
  let H := squareOrderHighVertices G d
  let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
    (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
  let k : V → Nat := fun x => (G.neighborFinset x ∩ H).card
  let r : Nat := d * d - H.card - (d + 1)
  dsimp only
  have hrow : ∀ x : V, (∑ y : V, C x y * C x y) =
      if x ∈ H then (r : ℤ) else ((H.card - k x : Nat) : ℤ) := by
    intro x
    simpa [C, H, k, r] using
      squareOrder_sum_commutator_entry_sq_row
        G hfree hd hmin hcover hcard x
  have hk_le : ∀ x : V, k x ≤ H.card := by
    intro x
    exact Finset.card_le_card Finset.inter_subset_right
  have hsumk : (∑ x : V, k x) = (d + 1) * H.card := by
    simpa [k, H] using squareOrder_sum_highNeighborCount_eq G d
  have hkhigh : ∀ x ∈ H, k x = 0 := by
    intro x hx
    simpa [k, H] using
      squareOrder_highNeighborCount_eq_zero_of_high G hcover hx
  by_cases hH : H = ∅
  · have hleft : (∑ x : V, ∑ y : V, C x y * C x y) = 0 := by
      calc
        _ = ∑ _x : V, (0 : ℤ) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [hrow x, if_neg (by simp [hH])]
          simp [hH]
        _ = 0 := by simp
    rw [hleft]
    change 0 = 2 * (H.card : ℤ) * (r : ℤ)
    simp [hH]
  · have hHpos : 0 < H.card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hH)
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hHpos
    have hcapacity : d + 1 ≤ d * d - H.card := by
      let L : Finset V := Finset.univ \ H
      have hsub : G.neighborFinset a ⊆ L := by
        intro y hy
        refine Finset.mem_sdiff.mpr ⟨by simp, ?_⟩
        intro hyH
        have hay : G.Adj a y := (G.mem_neighborFinset a y).mp hy
        exact squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover
          (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hyH).2 hay
      have hdeg : G.degree a = d + 1 := (Finset.mem_filter.mp ha).2
      have hLcard : L.card = d * d - H.card := by
        dsimp [L]
        rw [Finset.card_sdiff, Finset.card_univ, hcard]
        simp
      rw [← hdeg, ← G.card_neighborFinset_eq_degree, ← hLcard]
      exact Finset.card_le_card hsub
    have hr_cast : (r : ℤ) = (d * d : ℤ) - H.card - (d + 1) := by
      rw [show r = (d * d - H.card) - (d + 1) by rfl]
      rw [Nat.cast_sub hcapacity]
      rw [Nat.cast_sub]
      · norm_num
      · omega
    have hsplit : (∑ x : V, ∑ y : V, C x y * C x y) =
        (∑ x ∈ H, ∑ y : V, C x y * C x y) +
        (∑ x ∈ (Finset.univ \ H), ∑ y : V, C x y * C x y) := by
      rw [← Finset.sum_union]
      · congr 1
        exact (Finset.union_sdiff_of_subset (Finset.subset_univ H)).symm
      · exact Finset.disjoint_sdiff
    rw [hsplit]
    have hhigh : (∑ x ∈ H, ∑ y : V, C x y * C x y) =
        (H.card : ℤ) * r := by
      calc
        _ = ∑ _x ∈ H, (r : ℤ) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hrow x, if_pos hx]
        _ = _ := by simp
    have hsumkLow : (∑ x ∈ (Finset.univ \ H), k x) =
        (d + 1) * H.card := by
      have hsplitk := Finset.sum_sdiff
        (show H ⊆ (Finset.univ : Finset V) by simp) (f := k)
      have hzero : (∑ x ∈ H, k x) = 0 := Finset.sum_eq_zero hkhigh
      rw [hzero, add_zero] at hsplitk
      exact hsplitk.trans hsumk
    have hLcard : (Finset.univ \ H).card = d * d - H.card := by
      rw [Finset.card_sdiff, Finset.card_univ, hcard]
      simp
    have hHle : H.card ≤ d * d := by omega
    have hlow : (∑ x ∈ (Finset.univ \ H), ∑ y : V, C x y * C x y) =
        (H.card : ℤ) * r := by
      calc
        _ = ∑ x ∈ (Finset.univ \ H), ((H.card : ℤ) - k x) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxnot : x ∉ H := (Finset.mem_sdiff.mp hx).2
          rw [hrow x, if_neg hxnot, Nat.cast_sub (hk_le x)]
        _ = ((Finset.univ \ H).card : ℤ) * H.card -
            (∑ x ∈ (Finset.univ \ H), k x : Nat) := by
          rw [Finset.sum_sub_distrib]
          simp
        _ = (H.card : ℤ) * r := by
          rw [hsumkLow, hLcard, Nat.cast_sub hHle, hr_cast]
          push_cast
          ring
    rw [hhigh, hlow]
    ring

end

end Erdos85
