import Proofs.Erdos85SizeTwoMuNegOneExtremeIncidence
import Proofs.Erdos85TwoIncidenceShadowRegular

/-! # Two-regular shore shadows of the `mu = -1` extreme owner fibres -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Suppressing the eight degree-two extreme owners on either sign produces a
two-regular simple graph on the corresponding eight-point component shore. -/
theorem orderSixtyFour_sizeTwo_muNegOne_extremeOwner_shadows_twoRegular
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
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-1 : ℤ) * s z) :
    let Xp := MuNegOnePositiveShore (secondOrderDefectGraph G) c s
    let Xm := MuNegOneNegativeShore (secondOrderDefectGraph G) c s
    let Ep := MuNegOnePositiveExteriorFiber G s
    let Em := MuNegOneNegativeExteriorFiber G s
    let Rp : Xp → Ep → Prop := fun x z ↦ G.Adj x.1 z.1
    let Rm : Xm → Em → Prop := fun x z ↦ G.Adj x.1 z.1
    (∀ x, (twoIncidenceShadow Rp).degree x = 2) ∧
      ∀ x, (twoIncidenceShadow Rm).degree x = 2 := by
  classical
  dsimp only
  let Xp := MuNegOnePositiveShore (secondOrderDefectGraph G) c s
  let Xm := MuNegOneNegativeShore (secondOrderDefectGraph G) c s
  let Ep := MuNegOnePositiveExteriorFiber G s
  let Em := MuNegOneNegativeExteriorFiber G s
  let Rp : Xp → Ep → Prop := fun x z ↦ G.Adj x.1 z.1
  let Rm : Xm → Em → Prop := fun x z ↦ G.Adj x.1 z.1
  have hinc := orderSixtyFour_sizeTwo_muNegOne_extremeIncidence_twoRegular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hpairp : ∀ ⦃x y : Xp⦄ ⦃z w : Ep⦄, x ≠ y →
      Rp x z → Rp y z → Rp x w → Rp y w → z = w := by
    intro x y z w hxy hxz hyz hxw hyw
    apply Subtype.ext
    have hxyval : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
    apply Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1 hxyval)
    · exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hxz,
        (G.mem_neighborFinset _ _).mpr hyz⟩
    · exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hxw,
        (G.mem_neighborFinset _ _).mpr hyw⟩
  have hpairm : ∀ ⦃x y : Xm⦄ ⦃z w : Em⦄, x ≠ y →
      Rm x z → Rm y z → Rm x w → Rm y w → z = w := by
    intro x y z w hxy hxz hyz hxw hyw
    apply Subtype.ext
    have hxyval : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
    apply Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1 hxyval)
    · exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hxz,
        (G.mem_neighborFinset _ _).mpr hyz⟩
    · exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hxw,
        (G.mem_neighborFinset _ _).mpr hyw⟩
  exact ⟨twoIncidenceShadow_regular Rp 2 (fun x => (hinc.2.2.1 x).1)
      hinc.2.2.2.2.1 hpairp,
    twoIncidenceShadow_regular Rm 2 (fun x => (hinc.2.2.2.1 x).2)
      hinc.2.2.2.2.2 hpairm⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_extremeOwner_shadows_twoRegular
