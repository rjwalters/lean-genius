import Proofs.Erdos85SizeTwoMuNegFiveResidualTwoFactors
import Proofs.Erdos85SizeTwoMuNegFiveInternalShadows

/-!
# The `mu=-5` residuals are the internal shore shadows
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem simpleGraph_eq_of_adj_imp_of_degree_eq
    {X : Type*} [Fintype X] [DecidableEq X]
    (A B : SimpleGraph X) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (hsub : ∀ ⦃x y⦄, A.Adj x y → B.Adj x y)
    (hdeg : ∀ x, A.degree x = B.degree x) : A = B := by
  ext x y
  constructor
  · intro hxy
    exact hsub hxy
  · intro hxy
    have hfinSub : A.neighborFinset x ⊆ B.neighborFinset x := by
      intro z hz
      exact (B.mem_neighborFinset x z).mpr
        (hsub ((A.mem_neighborFinset x z).mp hz))
    have hcard : (A.neighborFinset x).card = (B.neighborFinset x).card := by
      rw [A.card_neighborFinset_eq_degree, B.card_neighborFinset_eq_degree,
        hdeg x]
    have heq := Finset.eq_of_subset_of_card_le hfinSub (by omega)
    exact (A.mem_neighborFinset x y).mp (heq ▸ (B.mem_neighborFinset x y).mpr hxy)

theorem orderSixtyFour_sizeTwo_muNegFive_residual_eq_internal_shadows
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
    let B := fun x : Xp => fun y : Xm => G.Adj x.1 y.1
    ∃ fp : Equiv.Perm Xp, ∃ fm : Equiv.Perm Xm,
      ∃ hfpinv : ∀ x, fp (fp x) = x, ∃ hfpne : ∀ x, fp x ≠ x,
      ∃ hfminv : ∀ x, fm (fm x) = x, ∃ hfmne : ∀ x, fm x ≠ x,
      twoIncidenceShadow B =
        ((twoIncidenceShadow Rp ⊔
          freeInvolutionMatchingGraph fp hfpinv hfpne)ᶜ) ∧
      twoIncidenceShadow (fun z x => B x z) =
        ((twoIncidenceShadow Rm ⊔
          freeInvolutionMatchingGraph fm hfminv hfmne)ᶜ) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let Sp := MuNegFiveExtremeFiber G c s 2
  let Sm := MuNegFiveExtremeFiber G c s (-2)
  let Rp := fun x : Xp => fun z : Sp => G.Adj x.1 z.1
  let Rm := fun x : Xm => fun z : Sm => G.Adj x.1 z.1
  let B := fun x : Xp => fun y : Xm => G.Adj x.1 y.1
  obtain ⟨fp, fm, hfpinv, hfpne, hfminv, hfmne,
      hfp, hfm, hresP, hresM⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_residual_twoFactors
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hint := orderSixtyFour_sizeTwo_muNegFive_internal_shadows_twoRegular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  let EP := twoIncidenceShadow Rp
  let EM := twoIncidenceShadow Rm
  let MP := freeInvolutionMatchingGraph fp hfpinv hfpne
  let MM := freeInvolutionMatchingGraph fm hfminv hfmne
  let IP := twoIncidenceShadow B
  let IM := twoIncidenceShadow (fun z x => B x z)
  have hsubP : ∀ ⦃x y⦄, IP.Adj x y → (EP ⊔ MP)ᶜ.Adj x y := by
    intro x y hxy
    obtain ⟨hne, z, hxz, hyz⟩ := hxy
    change G.Adj x.1 z.1 at hxz
    change G.Adj y.1 z.1 at hyz
    refine ⟨hne, ?_⟩
    rintro (hext | hmate)
    · obtain ⟨_, w, hxw, hyw⟩ := hext
      change G.Adj x.1 w.1 at hxw
      change G.Adj y.1 w.1 at hyw
      have hzw : z.1 = w.1 := Finset.card_le_one.mp
        (common_le_one_of_not_containsC4 hfree x.1 y.1
          (fun h => hne (Subtype.ext h))) z.1 (by simp [hxz, hyz])
          w.1 (by simp [hxw, hyw])
      exact w.2.1 (hzw ▸ z.2.1)
    · have hmate' : fp x = y := hmate
      exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree
        (fun h => hne (Subtype.ext h)) hxz hyz) ((hfp x y).mpr hmate')
  have hsubM : ∀ ⦃x y⦄, IM.Adj x y → (EM ⊔ MM)ᶜ.Adj x y := by
    intro x y hxy
    obtain ⟨hne, z, hxz, hyz⟩ := hxy
    change G.Adj z.1 x.1 at hxz
    change G.Adj z.1 y.1 at hyz
    refine ⟨hne, ?_⟩
    rintro (hext | hmate)
    · obtain ⟨_, w, hxw, hyw⟩ := hext
      change G.Adj x.1 w.1 at hxw
      change G.Adj y.1 w.1 at hyw
      have hzw : z.1 = w.1 := Finset.card_le_one.mp
        (common_le_one_of_not_containsC4 hfree x.1 y.1
          (fun h => hne (Subtype.ext h))) z.1
          (Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset _ _).mpr hxz.symm,
              (G.mem_neighborFinset _ _).mpr hyz.symm⟩)
          w.1 (by simp [hxw, hyw])
      exact w.2.1 (hzw ▸ z.2.1)
    · have hmate' : fm x = y := hmate
      exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree
        (fun h => hne (Subtype.ext h)) hxz.symm hyz.symm) ((hfm x y).mpr hmate')
  have heqP : IP = (EP ⊔ MP)ᶜ :=
    simpleGraph_eq_of_adj_imp_of_degree_eq IP (EP ⊔ MP)ᶜ hsubP
      (fun x => by rw [hint.1 x, hresP x])
  have heqM : IM = (EM ⊔ MM)ᶜ :=
    simpleGraph_eq_of_adj_imp_of_degree_eq IM (EM ⊔ MM)ᶜ hsubM
      (fun x => by rw [hint.2 x, hresM x])
  exact ⟨fp, fm, hfpinv, hfpne, hfminv, hfmne, heqP, heqM⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_residual_eq_internal_shadows
