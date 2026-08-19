import Proofs.Erdos85BipartiteTwoRegularHall
import Proofs.Erdos85BipartiteTwoRegularShadowIso
import Proofs.Erdos85SizeTwoMuNegFiveNeutralProjection

/-! # Isomorphism of the `mu=-5` neutral-projection shore shadows -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The two shore shadows induced by neutral two-edge paths have the same
graph structure. -/
theorem orderSixtyFour_sizeTwo_muNegFive_neutralProjection_shadows_iso
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
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-5 : ℤ) * s z) :
    let N := MuNegFiveNeutralProjection G c s
    Nonempty (twoIncidenceShadow N ≃g
      twoIncidenceShadow (fun y x => N x y)) := by
  classical
  dsimp only
  let N := MuNegFiveNeutralProjection G c s
  have hregular :=
    orderSixtyFour_sizeTwo_muNegFive_neutralProjection_biregular
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  obtain ⟨f, hf⟩ := twoRegularBipartite_exists_afterMatching
    N hregular.1 hregular.2
  exact ⟨hf.shadowIso⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_neutralProjection_shadows_iso
