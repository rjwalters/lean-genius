import Proofs.Erdos85SizeTwoMuNegFiveInternalNeutralDichotomy
import Proofs.Erdos85SizeTwoEigenlineCycleGridCoordinates
import Proofs.Erdos85SizeTwoEigenlineSixTenSectorCases

/-! # The mixed `6+10` sector is impossible at `mu=-5` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem orderSixtyFour_sizeTwo_muNegFive_sixTen_mixed_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (hshort : ∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 2)
    (hlong : ∀ x : c.supp, x ∈ b.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 0) : False := by
  classical
  let D := secondOrderDefectGraph G
  let H := G.induce c.supp
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let B := fun x : Xp => fun y : Xm => G.Adj x.1 y.1
  let N := MuNegFiveNeutralProjection G c s
  have hprofile := orderSixtyFour_sizeTwo_muNegFive_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hdeg : ∀ x, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) x
  have hflip : ∀ ⦃x y : c.supp⦄, H.Adj x y → s x.1 = -s y.1 := by
    intro x y hxy
    rcases hs_in x.1 x.2 with hx | hx <;>
      rcases hs_in y.1 y.2 with hy | hy
    · have hzero := ((hprofile.2.2 x.1 x.2).2 hx).1
      let C := (G.neighborFinset x.1).filter
        (fun z => D.connectedComponentMk z = c)
      let Cm := C.filter fun z => s z = -1
      have hyC : y.1 ∈ C := Finset.mem_filter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hxy,
        (ConnectedComponent.mem_supp_iff c y.1).mp y.2⟩
      have hymem : y.1 ∈ Cm := Finset.mem_filter.mpr ⟨hyC, hy⟩
      have : 0 < Cm.card := Finset.card_pos.mpr ⟨y.1, hymem⟩
      change Cm.card = 0 at hzero
      omega
    · rw [hx, hy]
    · rw [hx, hy]
      norm_num
    · have hzero := ((hprofile.2.2 x.1 x.2).1 hx).1
      let C := (G.neighborFinset x.1).filter
        (fun z => D.connectedComponentMk z = c)
      let Cp := C.filter fun z => s z = 1
      have hyC : y.1 ∈ C := Finset.mem_filter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hxy,
        (ConnectedComponent.mem_supp_iff c y.1).mp y.2⟩
      have hymem : y.1 ∈ Cp := Finset.mem_filter.mpr ⟨hyC, hy⟩
      have : 0 < Cp.card := Finset.card_pos.mpr ⟨y.1, hymem⟩
      change Cp.card = 0 at hzero
      omega
  let t : c.supp → ℤ := fun z => s z.1
  obtain ⟨coord⟩ := exists_sizeTwoCycleGridCoordinates H hdeg 3
    (by omega) a (by omega) t (fun z _ => hs_in z.1 z.2) (by
      intro x y hxy
      exact hflip hxy)
  let xp : Xp := ⟨(coord.pval 0).1, (coord.pval 0).2,
    (coord.p_mem_sign 0).2⟩
  have hrow := orderSixtyFour_sizeTwo_muNegFive_internal_neutral_row_dichotomy
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hcol := orderSixtyFour_sizeTwo_muNegFive_internal_neutral_column_dichotomy
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hNregular := orderSixtyFour_sizeTwo_muNegFive_neutralProjection_biregular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hcover : ∀ z : c.supp, z ∈ a.supp ∨ z ∈ b.supp := by
    intro z
    by_contra hz
    push Not at hz
    let A : Finset c.supp := a.supp.toFinite.toFinset
    let C : Finset c.supp := b.supp.toFinite.toFinset
    have hdisj : Disjoint A C := by
      rw [Finset.disjoint_left]
      intro w hwa hwb
      have hwa' : w ∈ a.supp := by simpa [A] using hwa
      have hwb' : w ∈ b.supp := by simpa [C] using hwb
      apply hab
      exact ((ConnectedComponent.mem_supp_iff a w).mp hwa').symm.trans
        ((ConnectedComponent.mem_supp_iff b w).mp hwb')
    have hcardAC : (A ∪ C).card = 16 := by
      rw [Finset.card_union_of_disjoint hdisj]
      have hA : A.card = 6 := by
        change a.supp.toFinite.toFinset.card = 6
        rw [← Set.ncard_eq_toFinset_card]
        exact ha
      have hC : C.card = 10 := by
        change b.supp.toFinite.toFinset.card = 10
        rw [← Set.ncard_eq_toFinset_card]
        exact hb
      omega
    have hsub : A ∪ C ⊆ (Finset.univ : Finset c.supp) := by simp
    have heq : A ∪ C = (Finset.univ : Finset c.supp) := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hcardAC, Finset.card_univ]
      change Fintype.card c.supp ≤ 16
      have hccard : Fintype.card c.supp = 16 := by
        calc
          Fintype.card c.supp = c.supp.ncard := by
            simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
          _ = 16 := by omega
      omega
    have : z ∈ A ∪ C := by rw [heq]; simp
    rcases Finset.mem_union.mp this with hza | hzb
    · exact hz.1 (by simpa [A] using hza)
    · exact hz.2 (by simpa [C] using hzb)
  let NR := (Finset.univ : Finset Xm).filter fun y => N xp y
  have hNRcard : NR.card = 2 := hNregular.1 xp
  let y1 : Xm := ⟨(coord.nval 1).1, (coord.nval 1).2,
    (coord.n_mem_sign 1).2⟩
  have hsubsingleton : NR ⊆ {y1} := by
    intro y hy
    have hNxy := (Finset.mem_filter.mp hy).2
    let ys : c.supp := ⟨y.1, y.2.1⟩
    have hya : ys ∈ a.supp := by
      rcases hcover ys with hya | hyb
      · exact hya
      · have hzeroY := hlong ys hyb
        rcases hcol y with hEq | hDisj
        · have hBxy : B xp y := (hEq.2 xp).2 hNxy
          have hsame : H.connectedComponentMk (coord.pval 0) =
              H.connectedComponentMk ys :=
            ConnectedComponent.connectedComponentMk_eq_of_adj hBxy
          have hpa : coord.pval 0 ∈ a.supp := (coord.p_mem_sign 0).1
          have : a = b := by
            calc
              a = H.connectedComponentMk (coord.pval 0) :=
                ((ConnectedComponent.mem_supp_iff a _).mp hpa).symm
              _ = H.connectedComponentMk ys := hsame
              _ = b := (ConnectedComponent.mem_supp_iff b _).mp hyb
          exact (hab this).elim
        · have hzeroY' : (triangleFreeEdgeGraph G).degree y.1 = 0 := by
            simpa [ys] using hzeroY
          omega
    obtain ⟨j, hj⟩ := coord.n_surjective ys hya y.2.2
    have hBnot : ¬ B xp y := by
      intro hBxy
      have htwoX := hshort (coord.pval 0) (coord.p_mem_sign 0).1
      rcases hrow xp with hEq | hDisj
      · have hzeroX : (triangleFreeEdgeGraph G).degree xp.1 = 0 := hEq.1
        have htwoX' : (triangleFreeEdgeGraph G).degree xp.1 = 2 := by
          simpa [xp] using htwoX
        omega
      · exact (hDisj.2 y hBxy) hNxy
    have hjnot : ¬ (j = 0 ∨ j = 0 - 1) := by
      intro hjbad
      apply hBnot
      change H.Adj (coord.pval 0) ys
      rw [← hj]
      exact (coord.adj_iff 0 j).2 hjbad
    have hjone : j = 1 := by
      fin_cases j
      · exact (hjnot (Or.inl rfl)).elim
      · rfl
      · exfalso
        apply hjnot
        right
        apply (ZMod.val_injective 3)
        rfl
    apply Finset.mem_singleton.mpr
    apply Subtype.ext
    change y.1 = (coord.nval 1).1
    calc
      y.1 = ys.1 := rfl
      _ = (coord.nval j).1 := congrArg Subtype.val hj.symm
      _ = (coord.nval 1).1 := by rw [hjone]
  have hle := Finset.card_le_card hsubsingleton
  simp only [Finset.card_singleton] at hle
  omega

/-- Consequently the `mu=-5` `6+10` stratum can only occupy the
both-all-triangle-free sector. -/
theorem orderSixtyFour_sizeTwo_muNegFive_sixTen_long_allTriangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2 := by
  have hshort :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_allTriangleFree
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb
  rcases binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
      G hfree (by omega) (by decide) hreg hcard c hc b with hzero | htwo
  · exact (orderSixtyFour_sizeTwo_muNegFive_sixTen_mixed_false
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab ha hb
        hshort hzero).elim
  · exact htwo

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sixTen_mixed_false
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sixTen_long_allTriangleFree
