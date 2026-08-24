import Proofs.Erdos85FinalDyadicOversizedExceptionalPure
import Proofs.Erdos85C4FreeSubsetCherryBound
import Proofs.Erdos85GadgetDegreeSquares

/-!
# Graph-facing terminal for the large pure exceptional branch

The existing arithmetic terminal only needs the two replication classes.
Here they are constructed canonically from the full-line family.  Final-layer
packing supplies replication at most three; the sole remaining structural
socket is replication at least two on the shore.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A pure full exceptional family of size strictly between `q` and
`2q-2` is impossible once every shore point has replication at least two. -/
theorem c4Free_binarySquare_pureLarge_fullLineCenters_impossible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hqc : q < (fullLineCenters G S q).card)
    (hc : (fullLineCenters G S q).card ≤ 2 * q - 2)
    (hshore : 2 * S.card = q * q + (fullLineCenters G S q).card)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q)
    (hrepLower : ∀ p ∈ S,
      2 ≤ (G.neighborFinset p ∩ fullLineCenters G S q).card) : False := by
  let C := fullLineCenters G S q
  let rep : V → ℕ := fun p => (G.neighborFinset p ∩ C).card
  let N₂ := S.filter fun p => rep p = 2
  let N₃ := S.filter fun p => rep p = 3
  have hm : 2 ≤ m := by omega
  have hregm : ∀ v, G.degree v = 2 * m := by simpa [hqm] using hreg
  have hcardm : Fintype.card V = 4 * m * m := by
    rw [hcard, hqm]
    ring
  have hlower : 2 * m * m - 2 * m + 1 ≤ S.card := by
    have hshore' : 2 * S.card =
        (2 * m) * (2 * m) + (fullLineCenters G S (2 * m)).card := by
      simpa [hqm] using hshore
    have hqc' : 2 * m < (fullLineCenters G S (2 * m)).card := by
      simpa [hqm] using hqc
    have hc' : (fullLineCenters G S (2 * m)).card ≤ 2 * (2 * m) - 2 := by
      simpa [hqm] using hc
    have hprod : 2 * m * (2 * m) = 4 * (m * m) := by ring
    rw [hprod] at hshore'
    rw [show 2 * m * m = 2 * (m * m) by ring]
    omega
  have hupper : S.card ≤ 2 * m * m + 2 * m - 1 := by
    have hshore' : 2 * S.card =
        (2 * m) * (2 * m) + (fullLineCenters G S (2 * m)).card := by
      simpa [hqm] using hshore
    have hqc' : 2 * m < (fullLineCenters G S (2 * m)).card := by
      simpa [hqm] using hqc
    have hc' : (fullLineCenters G S (2 * m)).card ≤ 2 * (2 * m) - 2 := by
      simpa [hqm] using hc
    have hprod : 2 * m * (2 * m) = 4 * (m * m) := by ring
    rw [hprod] at hshore'
    rw [show 2 * m * m = 2 * (m * m) by ring]
    omega
  have htri' : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = 2 * m := by
    intro v
    simpa [hqm] using htri v
  have hrepUpper : ∀ p ∈ S, rep p ≤ 3 := by
    intro p hp
    have hbound := binarySquare_finalLayer_exceptionalNeighbors_card_le_three
      G hfree hm hregm hcardm S hlower hupper htri' p
    have hfilter :
        (G.neighborFinset p).filter (fun w =>
          (G.neighborFinset w ∩ S).card = 0 ∨
          (G.neighborFinset w ∩ S).card = 2 * m) =
        G.neighborFinset p ∩ C := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_inter,
        mem_fullLineCenters, C]
      constructor
      · rintro ⟨hwp, hzero | hfull⟩
        · have hwEmpty : w ∈ emptyLineCenters G S :=
            (mem_emptyLineCenters G S w).mpr hzero
          rw [hempty] at hwEmpty
          simp at hwEmpty
        · exact ⟨hwp, by simpa [hqm] using hfull⟩
      · rintro ⟨hwp, hfull⟩
        exact ⟨hwp, Or.inr (by simpa [hqm] using hfull)⟩
    rw [hfilter] at hbound
    exact hbound
  have hcases : ∀ p ∈ S, rep p = 2 ∨ rep p = 3 := by
    intro p hp
    have hlo := hrepLower p hp
    change 2 ≤ rep p at hlo
    have hup := hrepUpper p hp
    omega
  have hdisj : Disjoint N₂ N₃ := by
    rw [Finset.disjoint_left]
    intro p hp₂ hp₃
    have h₂ := (Finset.mem_filter.mp hp₂).2
    have h₃ := (Finset.mem_filter.mp hp₃).2
    omega
  have hunion : N₂ ∪ N₃ = S := by
    apply Finset.Subset.antisymm
    · apply Finset.union_subset
      · intro p hp
        exact (Finset.mem_filter.mp hp).1
      · intro p hp
        exact (Finset.mem_filter.mp hp).1
    · intro p hp
      rcases hcases p hp with h₂ | h₃
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h₂⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h₃⟩)
  have hclasses : N₂.card + N₃.card = S.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hout : ∀ p ∉ S, rep p = 0 := by
    intro p hp
    rw [Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨w, hw⟩
    have hwp := (Finset.mem_inter.mp hw).1
    have hwFull := (mem_fullLineCenters G S q w).mp
      (Finset.mem_inter.mp hw).2
    have hpNw : p ∈ G.neighborFinset w := by
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hwp
    have heq : G.neighborFinset w ∩ S = G.neighborFinset w := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hwFull, G.card_neighborFinset_eq_degree, hreg]
    have hpInter : p ∈ G.neighborFinset w ∩ S := by
      rw [heq]
      exact hpNw
    exact hp (Finset.mem_inter.mp hpInter).2
  have hsumRestrict : (∑ p ∈ S, rep p) = ∑ p : V, rep p := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro p _ hp
    exact hout p hp
  have hsumAll : (∑ p : V, rep p) = q * C.card := by
    have hinc := sum_card_neighbor_inter_eq_sum_degree G C
    change (∑ p : V, rep p) = _
    rw [hinc]
    simp [hreg, Nat.mul_comm]
  have hsumClasses : (∑ p ∈ S, rep p) = 2 * N₂.card + 3 * N₃.card := by
    rw [← hunion, Finset.sum_union hdisj]
    have hsum₂ : (∑ p ∈ N₂, rep p) = 2 * N₂.card := by
      calc
        (∑ p ∈ N₂, rep p) = ∑ _p ∈ N₂, 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact (Finset.mem_filter.mp hp).2
        _ = 2 * N₂.card := by simp [Nat.mul_comm]
    have hsum₃ : (∑ p ∈ N₃, rep p) = 3 * N₃.card := by
      calc
        (∑ p ∈ N₃, rep p) = ∑ _p ∈ N₃, 3 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact (Finset.mem_filter.mp hp).2
        _ = 3 * N₃.card := by simp [Nat.mul_comm]
    rw [hsum₂, hsum₃]
  have hincidence : 2 * N₂.card + 3 * N₃.card = q * C.card := by
    rw [← hsumClasses, hsumRestrict, hsumAll]
  have hcherry :=
    sum_choose_card_neighbor_inter_le_choose_card_of_not_containsC4
      G hfree C
  have hcherryRestrict :
      (∑ p ∈ S, (rep p).choose 2) ≤ C.card.choose 2 := by
    calc
      (∑ p ∈ S, (rep p).choose 2) ≤
          ∑ p : V, (rep p).choose 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun _ _ _ => Nat.zero_le _)
      _ ≤ C.card.choose 2 := hcherry
  have hcherryClasses :
      (∑ p ∈ S, (rep p).choose 2) = N₂.card + 3 * N₃.card := by
    rw [← hunion, Finset.sum_union hdisj]
    have hsum₂ : (∑ p ∈ N₂, (rep p).choose 2) = N₂.card := by
      calc
        (∑ p ∈ N₂, (rep p).choose 2) = ∑ _p ∈ N₂, 1 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
          decide
        _ = N₂.card := by simp
    have hsum₃ : (∑ p ∈ N₃, (rep p).choose 2) = 3 * N₃.card := by
      calc
        (∑ p ∈ N₃, (rep p).choose 2) = ∑ _p ∈ N₃, 3 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
          decide
        _ = 3 * N₃.card := by simp [Nat.mul_comm]
    rw [hsum₂, hsum₃]
  have hpairs : 2 * N₂.card + 6 * N₃.card ≤ C.card * (C.card - 1) := by
    have hle : N₂.card + 3 * N₃.card ≤ C.card.choose 2 := by
      rw [← hcherryClasses]
      exact hcherryRestrict
    nlinarith [two_mul_choose_two C.card]
  exact binarySquare_pureLargeExceptional_impossible
    hq hqc hc hshore hclasses hincidence hpairs

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureLarge_fullLineCenters_impossible
