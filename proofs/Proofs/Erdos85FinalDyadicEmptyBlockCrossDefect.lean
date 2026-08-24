import Proofs.Erdos85FinalDyadicEmptyBlockDefectBoundary

/-!
# Cross-block defect routing for empty-center blocks

A point in one empty-center block has a defect neighbor in every other such
block.  Otherwise all points of the other block would require distinct common
neighbors, but the first empty center already consumes one of the available
common-neighbor slots.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every point in one neighborhood block has a second-order-defect neighbor
in a disjoint block whose centers are defect-adjacent. -/
theorem exists_secondOrderDefect_neighbor_in_other_neighborBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    {e f x : V} (hefD : (secondOrderDefectGraph G).Adj e f)
    (hx : x ∈ G.neighborFinset e) :
    ∃ y ∈ G.neighborFinset f,
      y ∈ (secondOrderDefectGraph G).neighborFinset x := by
  have hefNe : e ≠ f := fun h => by
    subst f
    exact (secondOrderDefectGraph G).loopless.irrefl e hefD
  have hblocks : G.neighborFinset e ∩ G.neighborFinset f = ∅ := by
    apply Finset.card_eq_zero.mp
    exact (secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree hefNe).mp hefD
  have hxNotF : x ∉ G.neighborFinset f := by
    intro hxf
    have : x ∈ G.neighborFinset e ∩ G.neighborFinset f :=
      Finset.mem_inter.mpr ⟨hx, hxf⟩
    simpa [hblocks] using this
  by_contra hnone
  push_neg at hnone
  have hright :
      (∑ y ∈ G.neighborFinset f,
        (G.neighborFinset y ∩ G.neighborFinset x).card) = q := by
    calc
      _ = ∑ _y ∈ G.neighborFinset f, 1 := by
        apply Finset.sum_congr rfl
        intro y hy
        have hxy : x ≠ y := fun h => hxNotF (h ▸ hy)
        have hyNotD : y ∉ (secondOrderDefectGraph G).neighborFinset x :=
          hnone y hy
        rw [Finset.inter_comm,
          card_common_eq_if_secondOrderDefect G hfree x y hxy,
          if_neg hyNotD]
      _ = (G.neighborFinset f).card := by simp
      _ = q := by rw [G.card_neighborFinset_eq_degree, hreg]
  have heN : e ∈ G.neighborFinset x :=
    (G.mem_neighborFinset x e).mpr
      ((G.mem_neighborFinset e x).mp hx).symm
  have heTerm : (G.neighborFinset e ∩ G.neighborFinset f).card = 0 := by
    simp [hblocks]
  have hleftLe :
      (∑ z ∈ G.neighborFinset x,
        (G.neighborFinset z ∩ G.neighborFinset f).card) ≤ q - 1 := by
    rw [← Finset.sum_erase_add _ _ heN, heTerm, add_zero]
    calc
      _ ≤ ∑ _z ∈ (G.neighborFinset x).erase e, 1 := by
        apply Finset.sum_le_sum
        intro z hz
        have hzf : z ≠ f := by
          intro h
          subst z
          exact hxNotF ((G.mem_neighborFinset f x).mpr
            ((G.mem_neighborFinset x f).mp
              (Finset.mem_of_mem_erase hz)).symm)
        exact common_le_one_of_not_containsC4 hfree z f hzf
      _ = ((G.neighborFinset x).erase e).card := by simp
      _ = q - 1 := by
        rw [Finset.card_erase_of_mem heN,
          G.card_neighborFinset_eq_degree, hreg]
  have hcomm := sum_card_neighbor_inter_comm G
    (G.neighborFinset x) (G.neighborFinset f)
  rw [hright] at hcomm
  rw [hcomm] at hleftLe
  have hqpos : 0 < q := by
    have : 0 < (G.neighborFinset e).card := Finset.card_pos.mpr ⟨x, hx⟩
    rwa [G.card_neighborFinset_eq_degree, hreg] at this
  omega

/-- Cross-block routing fits all other empty blocks into the outside-shore
defect neighborhood of one negative-high point.  Consequently the number of
empty centers is at most `2^j-r`. -/
theorem finalDyadic_emptyLineCenters_card_le_half_sub_r
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    (emptyLineCenters G S).card ≤ 2 ^ j - r := by
  let E := emptyLineCenters G S
  by_cases hE : E = ∅
  · simp [E, hE]
  have hENonempty : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
  obtain ⟨e, he⟩ := hENonempty
  have hqpos : 0 < q := by omega
  have hNe : (G.neighborFinset e).Nonempty := by
    apply Finset.card_pos.mp
    rw [G.card_neighborFinset_eq_degree, hreg]
    exact hqpos
  obtain ⟨x, hx⟩ := hNe
  have hex : ∀ f ∈ E.erase e, ∃ y,
      y ∈ G.neighborFinset f ∧
      y ∈ (secondOrderDefectGraph G).neighborFinset x := by
    intro f hf
    have hfData := Finset.mem_erase.mp hf
    obtain ⟨y, hyB, hyD⟩ :=
      exists_secondOrderDefect_neighbor_in_other_neighborBlock
        G hfree hreg (hemptyClique he hfData.2 hfData.1.symm) hx
    exact ⟨y, hyB, hyD⟩
  choose pick hpickB hpickD using hex
  let pick' : V → V := fun f => if hf : f ∈ E.erase e then pick f hf else f
  have hpickEq : ∀ f (hf : f ∈ E.erase e), pick' f = pick f hf := by
    intro f hf
    dsimp only [pick']
    rw [dif_pos hf]
  have hmaps : Set.MapsTo pick' (↑(E.erase e) : Set V)
      (↑((secondOrderDefectGraph G).neighborFinset x \ S) : Set V) := by
    intro f hf
    have hfFin : f ∈ E.erase e := hf
    have hfE : f ∈ E := Finset.mem_of_mem_erase hfFin
    have hpickM := finalDyadic_emptyCenter_neighborFinset_subset_negativeHigh
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique hfE (hpickB f hfFin)
    have hpickNotS : pick f hfFin ∉ S :=
      Finset.mem_compl.mp (Finset.mem_filter.mp hpickM).1
    rw [hpickEq f hfFin]
    exact Finset.mem_sdiff.mpr ⟨hpickD f hfFin, hpickNotS⟩
  have hinj : Set.InjOn pick' (↑(E.erase e) : Set V) := by
    intro f hf g hg hpick
    have hfFin : f ∈ E.erase e := hf
    have hgFin : g ∈ E.erase e := hg
    rw [hpickEq f hfFin, hpickEq g hgFin] at hpick
    by_contra hfg
    have hdisj := finalDyadic_emptyCenter_neighborFinset_disjoint
      G hfree S hemptyClique
        (Finset.mem_of_mem_erase hfFin)
        (Finset.mem_of_mem_erase hgFin) hfg
    have hpF : pick f hfFin ∈ G.neighborFinset f := hpickB f hfFin
    have hpG : pick f hfFin ∈ G.neighborFinset g :=
      hpick ▸ hpickB g hgFin
    exact (Finset.disjoint_left.mp hdisj hpF) hpG
  have hcardLe : (E.erase e).card ≤
      ((secondOrderDefectGraph G).neighborFinset x \ S).card :=
    Finset.card_le_card_of_injOn pick' hmaps hinj
  have hxM := finalDyadic_emptyCenter_neighborFinset_subset_negativeHigh
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique he hx
  have hcut : ((secondOrderDefectGraph G).neighborFinset x ∩ S).card =
      2 ^ j + r := (Finset.mem_filter.mp hxM).2
  have hDdegree : ((secondOrderDefectGraph G).neighborFinset x).card = q - 1 := by
    rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree,
      binarySquare_regular_secondOrderDefect_degree_eq G hfree (by omega)
        hreg hcard]
  have houtside :
      ((secondOrderDefectGraph G).neighborFinset x \ S).card =
        2 ^ j - 1 - r := by
    have hsplit := Finset.card_sdiff_add_card_inter
      ((secondOrderDefectGraph G).neighborFinset x) S
    rw [hDdegree, hcut, hqa] at hsplit
    omega
  rw [houtside] at hcardLe
  have heCard : (E.erase e).card = E.card - 1 :=
    Finset.card_erase_of_mem he
  rw [heCard] at hcardLe
  change E.card ≤ 2 ^ j - r
  have hEpos : 0 < E.card := Finset.card_pos.mpr ⟨e, he⟩
  omega

end

end Erdos85

#print axioms
  Erdos85.exists_secondOrderDefect_neighbor_in_other_neighborBlock
#print axioms Erdos85.finalDyadic_emptyLineCenters_card_le_half_sub_r
