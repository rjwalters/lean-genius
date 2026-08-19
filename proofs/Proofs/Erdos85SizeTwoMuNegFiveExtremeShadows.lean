import Proofs.Erdos85TwoIncidenceShadowRegular
import Proofs.Erdos85NegativeSizeTwoMuNegFiveRowSaturation
import Proofs.Erdos85SizeTwoMuNegFiveMatchingCoordinates

/-!
# Four-regular exterior shadows at `mu=-5`

The sixteen positive (respectively negative) extreme exterior vertices form
a `4`-by-`2` incidence design with the corresponding eight-point sign shore.
C4-freeness prevents a repeated pair, so its shadow on the shore is a
four-regular graph.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

abbrev MuNegFiveExtremeFiber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ) (value : ℤ) :=
  {z : V // z ∉ c.supp ∧
    (G.adjMatrix ℤ).mulVec s z + 2 * s z = value}

/-- The positive and negative extreme exterior incidence designs produce
four-regular shadow graphs on the respective order-eight shores. -/
theorem orderSixtyFour_sizeTwo_muNegFive_extreme_shadows_fourRegular
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
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-5 : ℤ) * s z) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegFivePositiveShore D c s
    let Xm := MuNegFiveNegativeShore D c s
    let Sp := MuNegFiveExtremeFiber G c s 2
    let Sm := MuNegFiveExtremeFiber G c s (-2)
    let Rp := fun x : Xp => fun z : Sp => G.Adj x.1 z.1
    let Rm := fun x : Xm => fun z : Sm => G.Adj x.1 z.1
    (∀ x, (twoIncidenceShadow Rp).degree x = 4) ∧
      ∀ x, (twoIncidenceShadow Rm).degree x = 4 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let Sp := MuNegFiveExtremeFiber G c s 2
  let Sm := MuNegFiveExtremeFiber G c s (-2)
  let Rp := fun x : Xp => fun z : Sp => G.Adj x.1 z.1
  let Rm := fun x : Xm => fun z : Sm => G.Adj x.1 z.1
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s (-5) hs_out hs_in hH hD
  have hmem : ∀ x, x ∈ c.supp ↔ D.connectedComponentMk x = c :=
    fun x => ConnectedComponent.mem_supp_iff c x
  have hsaturation :=
    orderSixtyFour_sizeTwo_muNegFive_extreme_rowSaturation_of_local
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have ha_split : ∀ x, (G.adjMatrix ℤ).mulVec s x =
      ∑ y ∈ (G.neighborFinset x).filter
        (fun y => D.connectedComponentMk y = c), s y := by
    intro x
    rw [adjMatrix_mulVec_apply, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : D.connectedComponentMk y = c
    · simp [hy]
    · rw [if_neg hy, hs_out y (fun h => hy ((hmem y).mp h))]
  have hcolumn (sval wval : ℤ)
      (hsval : sval = -1 ∨ sval = 1)
      (z : {z : V // z ∉ c.supp ∧
        (G.adjMatrix ℤ).mulVec s z + 2 * s z = wval})
      (hwval : wval = 2 * sval) :
      ((Finset.univ : Finset {x : V // x ∈ c.supp ∧ s x = sval}).filter
        fun x => G.Adj x.1 z.1).card = 2 := by
    have hsz : s z.1 = 0 := hs_out z.1 z.2.1
    have hsum : ∑ y ∈ (G.neighborFinset z.1).filter
        (fun y => D.connectedComponentMk y = c), s y = 2 * sval := by
      rw [← ha_split z.1]
      simpa [hsz, hwval] using z.2.2
    let C := (G.neighborFinset z.1).filter
      (fun y => D.connectedComponentMk y = c)
    have hCcard : C.card = 2 := P.componentNeighborCard z.1
    have hall : ∀ y ∈ C, s y = sval := by
      intro y hy
      have hyc : y ∈ c.supp :=
        (hmem y).mpr (Finset.mem_filter.mp hy).2
      obtain ⟨a, b, hab, hCab⟩ := Finset.card_eq_two.mp hCcard
      have hyab : y = a ∨ y = b := by
        have : y ∈ ({a, b} : Finset V) := by rwa [← hCab]
        simpa using this
      have haC : a ∈ C := by rw [hCab]; simp
      have hbC : b ∈ C := by rw [hCab]; simp
      have hac : a ∈ c.supp := (hmem a).mpr (Finset.mem_filter.mp haC).2
      have hbc : b ∈ c.supp := (hmem b).mpr (Finset.mem_filter.mp hbC).2
      have habSum : s a + s b = 2 * sval := by
        change ∑ t ∈ C, s t = 2 * sval at hsum
        simpa [hCab, hab] using hsum
      rcases hs_in a hac with ha | ha <;>
        rcases hs_in b hbc with hb | hb <;>
        rcases hsval with hsval | hsval <;>
        rcases hyab with rfl | rfl <;> omega
    have himage : Finset.image Subtype.val
        ((Finset.univ : Finset {x : V // x ∈ c.supp ∧ s x = sval}).filter
          fun x => G.Adj x.1 z.1) = C := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, C]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(G.mem_neighborFinset _ _).mpr hx.symm,
          (hmem x.1).mp x.2.1⟩
      · rintro ⟨hyz, hyc⟩
        have hyc' : y ∈ c.supp := (hmem y).mpr hyc
        refine ⟨⟨y, hyc', hall y (Finset.mem_filter.mpr ⟨hyz, hyc⟩)⟩,
          ?_, rfl⟩
        exact ((G.mem_neighborFinset _ _).mp hyz).symm
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset {x : V // x ∈ c.supp ∧ s x = sval}).filter
            fun x => G.Adj x.1 z.1)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = C.card := congrArg Finset.card himage
      _ = 2 := hCcard
  have hrowP : ∀ x : Xp,
      ((Finset.univ : Finset Sp).filter fun z => Rp x z).card = 4 := by
    intro x
    have hsat := (hsaturation x.1 x.2.1).1 x.2.2 |>.1
    let T := (((G.neighborFinset x.1).filter fun y => y ∉ c.supp).filter
      fun y => (G.adjMatrix ℤ).mulVec s y + 2 * s y = 2)
    have himage : Finset.image Subtype.val
        ((Finset.univ : Finset Sp).filter fun z => Rp x z) = T := by
      ext y
      simp [Sp, Rp, T, G.adj_comm, and_assoc]
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Sp).filter fun z => Rp x z)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = T.card := congrArg Finset.card himage
      _ = 4 := hsat
  have hrowM : ∀ x : Xm,
      ((Finset.univ : Finset Sm).filter fun z => Rm x z).card = 4 := by
    intro x
    have hsat := (hsaturation x.1 x.2.1).2 x.2.2 |>.1
    let T := (((G.neighborFinset x.1).filter fun y => y ∉ c.supp).filter
      fun y => (G.adjMatrix ℤ).mulVec s y + 2 * s y = -2)
    have himage : Finset.image Subtype.val
        ((Finset.univ : Finset Sm).filter fun z => Rm x z) = T := by
      ext y
      simp [Sm, Rm, T, G.adj_comm, and_assoc]
    calc
      _ = (Finset.image Subtype.val
          ((Finset.univ : Finset Sm).filter fun z => Rm x z)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = T.card := congrArg Finset.card himage
      _ = 4 := hsat
  have hcolP : ∀ z : Sp,
      ((Finset.univ : Finset Xp).filter fun x => Rp x z).card = 2 := by
    intro z
    exact hcolumn 1 2 (Or.inr rfl) z rfl
  have hcolM : ∀ z : Sm,
      ((Finset.univ : Finset Xm).filter fun x => Rm x z).card = 2 := by
    intro z
    exact hcolumn (-1) (-2) (Or.inl rfl) z (by norm_num)
  have hpairP : ∀ ⦃x y z w⦄, x ≠ y →
      Rp x z → Rp y z → Rp x w → Rp y w → z = w := by
    intro x y z w hxy hxz hyz hxw hyw
    change G.Adj x.1 z.1 at hxz
    change G.Adj y.1 z.1 at hyz
    change G.Adj x.1 w.1 at hxw
    change G.Adj y.1 w.1 at hyw
    apply Subtype.ext
    exact Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1
        (fun h => hxy (Subtype.ext h))) z.1 (by simp [hxz, hyz])
        w.1 (by simp [hxw, hyw])
  have hpairM : ∀ ⦃x y z w⦄, x ≠ y →
      Rm x z → Rm y z → Rm x w → Rm y w → z = w := by
    intro x y z w hxy hxz hyz hxw hyw
    change G.Adj x.1 z.1 at hxz
    change G.Adj y.1 z.1 at hyz
    change G.Adj x.1 w.1 at hxw
    change G.Adj y.1 w.1 at hyw
    apply Subtype.ext
    exact Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1
        (fun h => hxy (Subtype.ext h))) z.1 (by simp [hxz, hyz])
        w.1 (by simp [hxw, hyw])
  exact ⟨twoIncidenceShadow_regular Rp 4 hrowP hcolP hpairP,
    twoIncidenceShadow_regular Rm 4 hrowM hcolM hpairM⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_extreme_shadows_fourRegular
