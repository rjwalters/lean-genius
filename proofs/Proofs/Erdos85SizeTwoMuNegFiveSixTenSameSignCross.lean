import Proofs.Erdos85SizeTwoMuNegFiveSixTenCrossDegree
import Proofs.Erdos85SizeTwoMuNegFiveDefectNormalForm

/-! # Same-sign defect matching crosses the `6+10` split at `mu=-5` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The canonical same-sign defect mates of all short-cycle vertices lie on
the long cycle. -/
theorem orderSixtyFour_sizeTwo_muNegFive_sixTen_short_sameSignDefect_cross
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegFivePositiveShore D c s
    let Xm := MuNegFiveNegativeShore D c s
    ∃ fp : Equiv.Perm Xp, ∃ fm : Equiv.Perm Xm,
      (∀ x y, D.Adj x.1 y.1 ↔ fp x = y) ∧
      (∀ y z, D.Adj y.1 z.1 ↔ fm y = z) ∧
      (∀ x : Xp, (⟨x.1, x.2.1⟩ : c.supp) ∈ a.supp →
        (⟨(fp x).1, (fp x).2.1⟩ : c.supp) ∈ b.supp) ∧
      ∀ y : Xm, (⟨y.1, y.2.1⟩ : c.supp) ∈ a.supp →
        (⟨(fm y).1, (fm y).2.1⟩ : c.supp) ∈ b.supp := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := G.induce c.supp
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  obtain ⟨fp, fm, hfp, _hfpinv, _hfpne, hfm, _hfminv, _hfmne⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_sameSign_defect_matchings
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hA := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have hcover : ∀ z : c.supp, z ∈ a.supp ∨ z ∈ b.supp := by
    intro z
    by_contra hz
    push Not at hz
    let A : Finset c.supp := a.supp.toFinite.toFinset
    let B : Finset c.supp := b.supp.toFinite.toFinset
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro w hwa hwb
      apply hab
      exact ((ConnectedComponent.mem_supp_iff a w).mp (by simpa [A] using hwa)).symm.trans
        ((ConnectedComponent.mem_supp_iff b w).mp (by simpa [B] using hwb))
    have hcardAB : (A ∪ B).card = 16 := by
      rw [Finset.card_union_of_disjoint hdisj]
      have hAcard : A.card = 6 := by
        change a.supp.toFinite.toFinset.card = 6
        rw [← Set.ncard_eq_toFinset_card]
        exact ha
      have hBcard : B.card = 10 := by
        change b.supp.toFinite.toFinset.card = 10
        rw [← Set.ncard_eq_toFinset_card]
        exact hb
      omega
    have heq : A ∪ B = (Finset.univ : Finset c.supp) := by
      apply Finset.eq_of_subset_of_card_le (by simp)
      rw [hcardAB, Finset.card_univ]
      calc
        Fintype.card c.supp = c.supp.ncard := by
          simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
        _ = 16 := by omega
        _ ≤ 16 := le_rfl
    have : z ∈ A ∪ B := by rw [heq]; simp
    rcases Finset.mem_union.mp this with hza | hzb
    · exact hz.1 (by simpa [A] using hza)
    · exact hz.2 (by simpa [B] using hzb)
  have hnotShortPos (x : Xp) (hx : (⟨x.1, x.2.1⟩ : c.supp) ∈ a.supp) :
      (⟨(fp x).1, (fp x).2.1⟩ : c.supp) ∉ a.supp := by
    intro hfx
    have hDxf : D.Adj x.1 (fp x).1 := (hfp x (fp x)).2 rfl
    have hGxf :=
      (binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_defectAdj_iff
        G hfree hreg hcard c hc s hs_in hs_out hA a b ha hb
        (⟨x.1, x.2.1⟩ : c.supp) (⟨(fp x).1, (fp x).2.1⟩ : c.supp)
        hx hfx).1 hDxf
    have hmem : (fp x).1 ∈ componentNeighborFinset G D c x.1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hGxf,
        (ConnectedComponent.mem_supp_iff c _).mp (fp x).2.1⟩
    have hop := (internal_alternation G hfree (by omega) hreg hcard c
      (by simpa [Nat.mul_comm] using hc) s hs_in hs_out hA x.2.1).2 (fp x).1 hmem
    rw [x.2.2, (fp x).2.2] at hop
    omega
  have hnotShortNeg (y : Xm) (hy : (⟨y.1, y.2.1⟩ : c.supp) ∈ a.supp) :
      (⟨(fm y).1, (fm y).2.1⟩ : c.supp) ∉ a.supp := by
    intro hfy
    have hDyf : D.Adj y.1 (fm y).1 := (hfm y (fm y)).2 rfl
    have hGyf :=
      (binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_defectAdj_iff
        G hfree hreg hcard c hc s hs_in hs_out hA a b ha hb
        (⟨y.1, y.2.1⟩ : c.supp) (⟨(fm y).1, (fm y).2.1⟩ : c.supp)
        hy hfy).1 hDyf
    have hmem : (fm y).1 ∈ componentNeighborFinset G D c y.1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hGyf,
        (ConnectedComponent.mem_supp_iff c _).mp (fm y).2.1⟩
    have hop := (internal_alternation G hfree (by omega) hreg hcard c
      (by simpa [Nat.mul_comm] using hc) s hs_in hs_out hA y.2.1).2 (fm y).1 hmem
    rw [y.2.2, (fm y).2.2] at hop
    omega
  refine ⟨fp, fm, hfp, hfm, ?_, ?_⟩
  · intro x hx
    exact (hcover (⟨(fp x).1, (fp x).2.1⟩ : c.supp)).resolve_left
      (hnotShortPos x hx)
  · intro y hy
    exact (hcover (⟨(fm y).1, (fm y).2.1⟩ : c.supp)).resolve_left
      (hnotShortNeg y hy)

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sixTen_short_sameSignDefect_cross
