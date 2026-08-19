import Proofs.Erdos85SizeTwoMuNegFiveEightEightAllTriangleParameterBounds

/-! # Exact all-triangle parameter cases in the `mu=-5` C8+C8 branch -/

namespace Erdos85

noncomputable section

/-- On an all-triangle normalized C8 shore, the exact capacity equation and
`k≤1` leave only `(k,r)=(0,5)` or `(1,4)`. -/
theorem orderSixtyFour_sizeTwo_muNegFive_eightEight_allTriangle_parameter_cases
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
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hallA : ∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 0) :
    ∃ k r : ℕ, (k = 0 ∧ r = 5) ∨ (k = 1 ∧ r = 4) := by
  obtain ⟨k, r, hk, _hr2, _hr7, hcap⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_eightEight_allTriangle_parameter_bounds
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
      u v huinj hvinj hurange hvrange hu hv hallA
  refine ⟨k, r, ?_⟩
  omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_eightEight_allTriangle_parameter_cases

