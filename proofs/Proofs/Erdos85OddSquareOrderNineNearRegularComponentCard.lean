import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileBinZeroDefectTypes

/-! # Shore cardinality in the q=9 three-high second profile

The low vertices have incidence bins zero through four.  In the second
three-high profile bins two and four are empty and bin three is the unique
owner.  Hence every low shore omitting that owner consists exactly of its
bin-zero and bin-one parts.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A low shore omitting the unique bin-three point is partitioned by bins
zero and one.  This supplies the cardinality input to the `3 : 5` balance
terminal independently of any component-closure hypothesis. -/
theorem squareOrderNine_threeHigh_secondProfile_nonowner_shore_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (owner : V) (hownerB3 : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S : Finset V)
    (hSsub : S ⊆
      (Finset.univ : Finset V) \ squareOrderHighVertices G 9)
    (hownerS : owner ∉ S) :
    S.card =
      (squareOrderNineLowIncidenceBin G 0 ∩ S).card +
        (squareOrderNineLowIncidenceBin G 1 ∩ S).card := by
  classical
  let H := squareOrderHighVertices G 9
  let B := squareOrderNineLowIncidenceBin G
  let k := squareOrderHighIncidenceCount G 9
  have hB2 : B 2 = ∅ := by
    rw [← Finset.card_eq_zero]
    dsimp only [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 2) (by omega), hc2]
  have hB4 : B 4 = ∅ := by
    rw [← Finset.card_eq_zero]
    dsimp only [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 4) (by omega), hc4]
  have hB3card : (B 3).card = 1 := by
    dsimp only [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hpartition : S = (B 0 ∩ S) ∪ (B 1 ∩ S) := by
    ext x
    constructor
    · intro hxS
      have hxLow : G.degree x = 9 := by
        rcases hp.degree_dichotomy x with hx | hx
        · exact hx
        · have hxH : x ∈ H := by
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
          exact ((Finset.mem_sdiff.mp (hSsub hxS)).2 hxH).elim
      have hkbound := hp.low_incidence_bound hxLow
      change 2 * k x ≤ 9 at hkbound
      have hxBk : x ∈ B (k x) := by
        exact Finset.mem_filter.mpr ⟨hSsub hxS, rfl⟩
      have hcases : k x = 0 ∨ k x = 1 ∨ k x = 2 ∨ k x = 3 ∨ k x = 4 := by
        omega
      rcases hcases with hk | hk | hk | hk | hk
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨by simpa [hk] using hxBk, hxS⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨by simpa [hk] using hxBk, hxS⟩)
      · have : x ∈ B 2 := by simpa [hk] using hxBk
        rw [hB2] at this
        exact (Finset.notMem_empty x this).elim
      · have hxB3 : x ∈ B 3 := by simpa [hk] using hxBk
        have hxOwner : x = owner :=
          Finset.card_le_one.mp (by omega) x hxB3 owner hownerB3
        exact (hownerS (hxOwner ▸ hxS)).elim
      · have : x ∈ B 4 := by simpa [hk] using hxBk
        rw [hB4] at this
        exact (Finset.notMem_empty x this).elim
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).2
      · exact (Finset.mem_inter.mp hx).2
  have hdisj : Disjoint (B 0 ∩ S) (B 1 ∩ S) := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    have h0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx0).1).2
    have h1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx1).1).2
    omega
  calc
    S.card = ((B 0 ∩ S) ∪ (B 1 ∩ S)).card := congrArg Finset.card hpartition
    _ = (B 0 ∩ S).card + (B 1 ∩ S).card :=
      Finset.card_union_of_disjoint hdisj

#print axioms squareOrderNine_threeHigh_secondProfile_nonowner_shore_card

end

end Erdos85
