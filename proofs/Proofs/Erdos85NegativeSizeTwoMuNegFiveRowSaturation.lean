import Proofs.Erdos85NegativeSizeTwoExtremeRowBalance
import Proofs.Erdos85BinarySquareSizeTwoNegativeSupportProfiles

/-! # Row saturation at the extreme negative size-two eigenvalue -/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- At `μ = -5`, every positive component row is saturated by exactly four
positive extreme exterior cells and no negative extreme cells; the negative
rows satisfy the dual statement. -/
theorem orderSixtyFour_sizeTwo_muNegFive_extreme_rowSaturation_of_local
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
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = (-5 : ℤ) * s z) :
    let w := fun x ↦ (G.adjMatrix ℤ).mulVec s x + 2 * s x
    let p := fun x ↦ (((G.neighborFinset x).filter
      (fun y ↦ y ∉ c.supp)).filter fun y ↦ w y = 2).card
    let n := fun x ↦ (((G.neighborFinset x).filter
      (fun y ↦ y ∉ c.supp)).filter fun y ↦ w y = -2).card
    ∀ x, x ∈ c.supp →
      (s x = 1 → p x = 4 ∧ n x = 0) ∧
      (s x = -1 → n x = 4 ∧ p x = 0) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let w : V → ℤ := fun x ↦ A.mulVec s x + 2 * s x
  let T := fun x ↦ (G.neighborFinset x).filter fun y ↦ y ∉ c.supp
  let p := fun x ↦ ((T x).filter fun y ↦ w y = 2).card
  let n := fun x ↦ ((T x).filter fun y ↦ w y = -2).card
  let Xp : Finset V := Finset.univ.filter fun x ↦ x ∈ c.supp ∧ s x = 1
  let Xm : Finset V := Finset.univ.filter fun x ↦ x ∈ c.supp ∧ s x = -1
  let Sp : Finset V := Finset.univ.filter fun x ↦ w x = 2
  let Sm : Finset V := Finset.univ.filter fun x ↦ w x = -2
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s (-5) hs_out hs_in hH hD
  have hmem : ∀ x, x ∈ c.supp ↔
      (secondOrderDefectGraph G).connectedComponentMk x = c :=
    fun x ↦ ConnectedComponent.mem_supp_iff c x
  have hXp_mem : ∀ x, x ∈ Xp ↔ x ∈ c.supp ∧ s x = 1 := by
    intro x
    simp [Xp]
  have hXm_mem : ∀ x, x ∈ Xm ↔ x ∈ c.supp ∧ s x = -1 := by
    intro x
    simp [Xm]
  have hSp_mem : ∀ x, x ∈ Sp ↔ w x = 2 := by
    intro x
    simp [Sp]
  have hSm_mem : ∀ x, x ∈ Sm ↔ w x = -2 := by
    intro x
    simp [Sm]
  have hScard : (Finset.univ.filter fun x ↦ x ∈ c.supp).card = 16 := by
    calc
      _ = c.supp.toFinset.card := by
        congr
        ext x
        simp
      _ = c.supp.ncard := (Set.ncard_eq_toFinset_card' c.supp).symm
      _ = 16 := by omega
  have hshore : Xp.card = 8 ∧ Xm.card = 8 := by
    have hpartition : (Finset.univ.filter fun x ↦ x ∈ c.supp) = Xp ∪ Xm := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        hXp_mem, hXm_mem]
      constructor
      · intro hx
        rcases hs_in x hx with hs | hs
        · exact Or.inr ⟨hx, hs⟩
        · exact Or.inl ⟨hx, hs⟩
      · rintro (hx | hx) <;> exact hx.1
    have hdisj : Disjoint Xp Xm := by
      rw [Finset.disjoint_left]
      intro x hp hm
      have hp' := (hXp_mem x).mp hp
      have hm' := (hXm_mem x).mp hm
      omega
    have hcards : Xp.card + Xm.card = 16 := by
      rw [← Finset.card_union_of_disjoint hdisj, ← hpartition, hScard]
    have hsum : (Xp.card : ℤ) - Xm.card = 0 := by
      have hsumc := P.componentSum_eq_zero
      have heq : Finset.univ.filter
          (fun x ↦ (secondOrderDefectGraph G).connectedComponentMk x = c) = Xp ∪ Xm := by
        rw [← hpartition]
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hmem x).symm
      rw [heq, Finset.sum_union hdisj] at hsumc
      have hp : ∑ x ∈ Xp, s x = (Xp.card : ℤ) := by
        rw [Finset.sum_congr rfl (fun x hx ↦ (hXp_mem x).mp hx |>.2)]
        simp
      have hm : ∑ x ∈ Xm, s x = -(Xm.card : ℤ) := by
        rw [Finset.sum_congr rfl (fun x hx ↦ (hXm_mem x).mp hx |>.2)]
        simp
      rw [hp, hm] at hsumc
      exact hsumc
    omega
  have hprofile := orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
    G hfree hreg hcard c hc s (-5) hs_out hs_in hH hD
  change Sp.card = Sm.card ∧
    4 * (Sp.card : ℤ) = 8 * (3 - (-5 : ℤ)) ∧ _ at hprofile
  have hSpcard : Sp.card = 16 := by omega
  have ha_split : ∀ x, A.mulVec s x = ∑ y ∈ (G.neighborFinset x).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c), s y := by
    intro x
    rw [adjMatrix_mulVec_apply]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : (secondOrderDefectGraph G).connectedComponentMk y = c
    · simp [hy]
    · rw [if_neg hy, hs_out y (fun h ↦ hy ((hmem y).mp h))]
  have hSp_out : ∀ u ∈ Sp, u ∉ c.supp := by
    intro u hu huc
    have hwu := (hSp_mem u).mp hu
    have hA := P.ambientAction_in u huc
    change A.mulVec s u = -2 * s u at hA
    change A.mulVec s u + 2 * s u = 2 at hwu
    omega
  have hSpdeg : ∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Xp).card = 2 := by
    intro u hu
    have hwu := (hSp_mem u).mp hu
    have huc := hSp_out u hu
    have hsu := hs_out u huc
    change A.mulVec s u + 2 * s u = 2 at hwu
    rw [hsu] at hwu
    simp only [mul_zero, add_zero] at hwu
    rw [ha_split u] at hwu
    let C := (G.neighborFinset u).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c)
    have hCcard : C.card = 2 := P.componentNeighborCard u
    have hall : ∀ y ∈ C, s y = 1 := by
      intro y hy
      have hyC := hy
      change y ∈ (G.neighborFinset u).filter
        (fun z ↦ (secondOrderDefectGraph G).connectedComponentMk z = c) at hy
      have hyc : y ∈ c.supp := (hmem y).mpr (Finset.mem_filter.mp hy).2
      rcases hs_in y hyc with hs | hs
      · exfalso
        have hle : ∑ z ∈ C, s z ≤ 0 := by
          obtain ⟨a, b, hab, hC⟩ := Finset.card_eq_two.mp hCcard
          rw [hC, Finset.sum_pair hab]
          have hyab : y = a ∨ y = b := by
            have : y ∈ ({a, b} : Finset V) := by
              rw [← hC]
              exact hyC
            simpa using this
          rcases hyab with rfl | rfl
          · rw [hs]
            have hb : b ∈ c.supp := (hmem b).mpr (Finset.mem_filter.mp
              (show b ∈ C by rw [hC]; simp)).2
            rcases hs_in b hb with hb | hb <;> rw [hb] <;> norm_num
          · rw [hs]
            have ha : a ∈ c.supp := (hmem a).mpr (Finset.mem_filter.mp
              (show a ∈ C by rw [hC]; simp)).2
            rcases hs_in a ha with ha | ha <;> rw [ha] <;> norm_num
        change (∑ z ∈ C, s z) = 2 at hwu
        omega
      · exact hs
    have heq : (G.neighborFinset u).filter (fun y ↦ y ∈ Xp) =
        (G.neighborFinset u).filter
          (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c) := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hy, hyXp⟩
        exact ⟨hy, (hmem y).mp ((hXp_mem y).mp hyXp).1⟩
      · rintro ⟨hy, hyc⟩
        exact ⟨hy, (hXp_mem y).mpr ⟨(hmem y).mpr hyc,
          hall y (Finset.mem_filter.mpr ⟨hy, hyc⟩)⟩⟩
    rw [heq, P.componentNeighborCard u]
  have hdc := sum_sum_filter_neighborFinset_comm G Xp Sp (fun _ _ ↦ (1 : ℤ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hdc
  have hsumP : ∑ x ∈ Xp, (p x : ℤ) = 32 := by
    have hleft : ∑ x ∈ Xp,
        (((G.neighborFinset x).filter fun y ↦ y ∈ Sp).card : ℤ) =
        ∑ x ∈ Xp, (p x : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      norm_cast
      apply congrArg Finset.card
      ext y
      simp only [Finset.mem_filter, hSp_mem, T]
      constructor
      · rintro ⟨hxy, hwy⟩
        have hyout : y ∉ c.supp := by
          intro hyc
          have hA := P.ambientAction_in y hyc
          change A.mulVec s y = -2 * s y at hA
          change A.mulVec s y + 2 * s y = 2 at hwy
          omega
        exact ⟨⟨hxy, hyout⟩, hwy⟩
      · rintro ⟨⟨hxy, _⟩, hwy⟩
        exact ⟨hxy, hwy⟩
    have hright : ∑ u ∈ Sp,
        (((G.neighborFinset u).filter fun y ↦ y ∈ Xp).card : ℤ) = 32 := by
      rw [Finset.sum_congr rfl (fun u hu ↦ by rw [hSpdeg u hu])]
      rw [Finset.sum_const, nsmul_eq_mul, hSpcard]
      norm_num
    rw [hleft, hright] at hdc
    exact hdc
  have hrow := orderSixtyFour_sizeTwo_negative_extreme_rowBalance_of_local
    G hfree hreg hcard c hc s (-5) (Or.inr (Or.inr rfl)) hs_out hs_in hH hD
  have hpos : ∀ x ∈ Xp, p x = n x + 4 := by
    intro x hx
    have hx' := (hXp_mem x).mp hx
    rcases hrow x hx'.1 with h | h
    · rcases h.2 with h | h | h
      · omega
      · omega
      · exact h.2
    · omega
  have hsumN : ∑ x ∈ Xp, n x = 0 := by
    have hs : ∑ x ∈ Xp, (p x : ℤ) =
        ∑ x ∈ Xp, (n x : ℤ) + 4 * Xp.card := by
      calc
        _ = ∑ x ∈ Xp, ((n x + 4 : ℕ) : ℤ) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hpos x hx]
        _ = _ := by
          simp only [Nat.cast_add, Nat.cast_ofNat, Finset.sum_add_distrib,
            Finset.sum_const, nsmul_eq_mul]
          ring
    rw [hsumP, hshore.1] at hs
    norm_num at hs
    exact_mod_cast hs
  have hnzero : ∀ x ∈ Xp, n x = 0 := by
    exact Finset.sum_eq_zero_iff.mp hsumN
  have hplus : ∀ x, x ∈ c.supp → s x = 1 → p x = 4 ∧ n x = 0 := by
    intro x hx hs
    have hxXp : x ∈ Xp := (hXp_mem x).mpr ⟨hx, hs⟩
    have hn := hnzero x hxXp
    have hp := hpos x hxXp
    exact ⟨by omega, hn⟩
  have hSmcard : Sm.card = 16 := by omega
  have hSm_out : ∀ u ∈ Sm, u ∉ c.supp := by
    intro u hu huc
    have hwu := (hSm_mem u).mp hu
    have hA := P.ambientAction_in u huc
    change A.mulVec s u = -2 * s u at hA
    change A.mulVec s u + 2 * s u = -2 at hwu
    omega
  have hSmdeg : ∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Xm).card = 2 := by
    intro u hu
    have hwu := (hSm_mem u).mp hu
    have huc := hSm_out u hu
    have hsu := hs_out u huc
    change A.mulVec s u + 2 * s u = -2 at hwu
    rw [hsu] at hwu
    simp only [mul_zero, add_zero] at hwu
    rw [ha_split u] at hwu
    let C := (G.neighborFinset u).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c)
    have hCcard : C.card = 2 := P.componentNeighborCard u
    have hall : ∀ y ∈ C, s y = -1 := by
      intro y hy
      have hyC := hy
      change y ∈ (G.neighborFinset u).filter
        (fun z ↦ (secondOrderDefectGraph G).connectedComponentMk z = c) at hy
      have hyc : y ∈ c.supp := (hmem y).mpr (Finset.mem_filter.mp hy).2
      rcases hs_in y hyc with hs | hs
      · exact hs
      · exfalso
        have hge : 0 ≤ ∑ z ∈ C, s z := by
          obtain ⟨a, b, hab, hC⟩ := Finset.card_eq_two.mp hCcard
          rw [hC, Finset.sum_pair hab]
          have hyab : y = a ∨ y = b := by
            have : y ∈ ({a, b} : Finset V) := by
              rw [← hC]
              exact hyC
            simpa using this
          rcases hyab with rfl | rfl
          · rw [hs]
            have hb : b ∈ c.supp := (hmem b).mpr (Finset.mem_filter.mp
              (show b ∈ C by rw [hC]; simp)).2
            rcases hs_in b hb with hb | hb <;> rw [hb] <;> norm_num
          · rw [hs]
            have ha : a ∈ c.supp := (hmem a).mpr (Finset.mem_filter.mp
              (show a ∈ C by rw [hC]; simp)).2
            rcases hs_in a ha with ha | ha <;> rw [ha] <;> norm_num
        change (∑ z ∈ C, s z) = -2 at hwu
        omega
    have heq : (G.neighborFinset u).filter (fun y ↦ y ∈ Xm) =
        (G.neighborFinset u).filter
          (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c) := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hy, hyXm⟩
        exact ⟨hy, (hmem y).mp ((hXm_mem y).mp hyXm).1⟩
      · rintro ⟨hy, hyc⟩
        exact ⟨hy, (hXm_mem y).mpr ⟨(hmem y).mpr hyc,
          hall y (Finset.mem_filter.mpr ⟨hy, hyc⟩)⟩⟩
    rw [heq, P.componentNeighborCard u]
  have hdcM := sum_sum_filter_neighborFinset_comm G Xm Sm (fun _ _ ↦ (1 : ℤ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hdcM
  have hsumM : ∑ x ∈ Xm, (n x : ℤ) = 32 := by
    have hleft : ∑ x ∈ Xm,
        (((G.neighborFinset x).filter fun y ↦ y ∈ Sm).card : ℤ) =
        ∑ x ∈ Xm, (n x : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      norm_cast
      apply congrArg Finset.card
      ext y
      simp only [Finset.mem_filter, hSm_mem, T]
      constructor
      · rintro ⟨hxy, hwy⟩
        have hyout : y ∉ c.supp := by
          intro hyc
          have hA := P.ambientAction_in y hyc
          change A.mulVec s y = -2 * s y at hA
          change A.mulVec s y + 2 * s y = -2 at hwy
          omega
        exact ⟨⟨hxy, hyout⟩, hwy⟩
      · rintro ⟨⟨hxy, _⟩, hwy⟩
        exact ⟨hxy, hwy⟩
    have hright : ∑ u ∈ Sm,
        (((G.neighborFinset u).filter fun y ↦ y ∈ Xm).card : ℤ) = 32 := by
      rw [Finset.sum_congr rfl (fun u hu ↦ by rw [hSmdeg u hu])]
      rw [Finset.sum_const, nsmul_eq_mul, hSmcard]
      norm_num
    rw [hleft, hright] at hdcM
    exact hdcM
  have hneg : ∀ x ∈ Xm, n x = p x + 4 := by
    intro x hx
    have hx' := (hXm_mem x).mp hx
    rcases hrow x hx'.1 with h | h
    · omega
    · rcases h.2 with h | h | h
      · omega
      · omega
      · exact h.2
  have hsumPzero : ∑ x ∈ Xm, p x = 0 := by
    have hs : ∑ x ∈ Xm, (n x : ℤ) =
        ∑ x ∈ Xm, (p x : ℤ) + 4 * Xm.card := by
      calc
        _ = ∑ x ∈ Xm, ((p x + 4 : ℕ) : ℤ) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hneg x hx]
        _ = _ := by
          simp only [Nat.cast_add, Nat.cast_ofNat, Finset.sum_add_distrib,
            Finset.sum_const, nsmul_eq_mul]
          ring
    rw [hsumM, hshore.2] at hs
    norm_num at hs
    exact_mod_cast hs
  have hpzero : ∀ x ∈ Xm, p x = 0 := Finset.sum_eq_zero_iff.mp hsumPzero
  have hminus : ∀ x, x ∈ c.supp → s x = -1 → n x = 4 ∧ p x = 0 := by
    intro x hx hs
    have hxXm : x ∈ Xm := (hXm_mem x).mpr ⟨hx, hs⟩
    have hp := hpzero x hxXm
    have hn := hneg x hxXm
    exact ⟨by omega, hp⟩
  intro x hx
  exact ⟨hplus x hx, hminus x hx⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_extreme_rowSaturation_of_local
