import Proofs.Erdos85SizeTwoMuNegFiveSixTenMixedExclusion

/-! # Neutral cross-cycle incidence in the `mu=-5`, `6+10` sector -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem zmodThree_eq_add_one_of_not_eq_or_eq_sub_one
    (i j : ZMod 3) (h : ¬ (j = i ∨ j = i - 1)) : j = i + 1 := by
  revert i j
  decide

/-- Every positive vertex of the short cycle has a neutral-projection partner
on the long cycle. -/
theorem orderSixtyFour_sizeTwo_muNegFive_sixTen_short_positive_neutralCross_exists
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
      (triangleFreeEdgeGraph G).degree x.1 = 2) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegFivePositiveShore D c s
    let Xm := MuNegFiveNegativeShore D c s
    let N := MuNegFiveNeutralProjection G c s
    ∀ x : Xp, (⟨x.1, x.2.1⟩ : c.supp) ∈ a.supp →
      ∃ y : Xm, N x y ∧ (⟨y.1, y.2.1⟩ : c.supp) ∈ b.supp := by
  classical
  dsimp only
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
    · rw [hx, hy]; norm_num
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
  have hrow := orderSixtyFour_sizeTwo_muNegFive_internal_neutral_row_dichotomy
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
      apply hab
      exact ((ConnectedComponent.mem_supp_iff a w).mp (by simpa [A] using hwa)).symm.trans
        ((ConnectedComponent.mem_supp_iff b w).mp (by simpa [C] using hwb))
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
    have heq : A ∪ C = (Finset.univ : Finset c.supp) := by
      apply Finset.eq_of_subset_of_card_le (by simp)
      rw [hcardAC, Finset.card_univ]
      change Fintype.card c.supp ≤ 16
      calc
        Fintype.card c.supp = c.supp.ncard := by
          simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
        _ = 16 := by omega
        _ ≤ 16 := le_rfl
    have : z ∈ A ∪ C := by rw [heq]; simp
    rcases Finset.mem_union.mp this with hza | hzb
    · exact hz.1 (by simpa [A] using hza)
    · exact hz.2 (by simpa [C] using hzb)
  intro x hxa
  obtain ⟨i, hi⟩ := coord.p_surjective (⟨x.1, x.2.1⟩ : c.supp) hxa x.2.2
  by_contra hcross
  push Not at hcross
  let NR := (Finset.univ : Finset Xm).filter fun y => N x y
  have hNRcard : NR.card = 2 := hNregular.1 x
  let y1 : Xm := ⟨(coord.nval (i + 1)).1, (coord.nval (i + 1)).2,
    (coord.n_mem_sign (i + 1)).2⟩
  have hsubsingleton : NR ⊆ {y1} := by
    intro y hy
    have hNxy := (Finset.mem_filter.mp hy).2
    let ys : c.supp := ⟨y.1, y.2.1⟩
    have hya : ys ∈ a.supp := by
      rcases hcover ys with hya | hyb
      · exact hya
      · exact (hcross y hNxy hyb).elim
    obtain ⟨j, hj⟩ := coord.n_surjective ys hya y.2.2
    have hBnot : ¬ B x y := by
      intro hBxy
      rcases hrow x with hEq | hDisj
      · have htwo := hshort (⟨x.1, x.2.1⟩ : c.supp) hxa
        have htwo' : (triangleFreeEdgeGraph G).degree x.1 = 2 := by
          simpa using htwo
        omega
      · exact (hDisj.2 y hBxy) hNxy
    have hjnot : ¬ (j = i ∨ j = i - 1) := by
      intro hjbad
      apply hBnot
      change H.Adj (⟨x.1, x.2.1⟩ : c.supp) ys
      rw [← hi, ← hj]
      exact (coord.adj_iff i j).2 hjbad
    have hjone : j = i + 1 :=
      zmodThree_eq_add_one_of_not_eq_or_eq_sub_one i j hjnot
    apply Finset.mem_singleton.mpr
    apply Subtype.ext
    change y.1 = (coord.nval (i + 1)).1
    calc
      y.1 = ys.1 := rfl
      _ = (coord.nval j).1 := congrArg Subtype.val hj.symm
      _ = (coord.nval (i + 1)).1 := by rw [hjone]
  have hle := Finset.card_le_card hsubsingleton
  simp only [Finset.card_singleton] at hle
  omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_sixTen_short_positive_neutralCross_exists
