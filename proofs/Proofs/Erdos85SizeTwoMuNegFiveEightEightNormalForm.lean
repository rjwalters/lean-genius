import Proofs.Erdos85SizeTwoMuNegFiveEightEightCrossSameMatching
import Proofs.Erdos85SizeTwoMuNegFiveEightEightCrossSameEmpty
import Proofs.Erdos85SizeTwoMuNegFiveEightEightParameterBounds

/-! # Exact signed normal forms in the `mu=-5` C8+C8 branch -/

open Finset

namespace Erdos85

noncomputable section

set_option maxHeartbeats 1200000 in
/-- In normalized C8 coordinates, the `mu=-5` branch has exactly two signed
cross-block forms: `k=0` gives an oriented same-sign perfect matching, while
`k=1` gives an empty same-sign cross block. -/
theorem orderSixtyFour_sizeTwo_muNegFive_eightEight_signed_normalForm
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
      {v (z - 1), v (z + 1)}) :
    ∃ k r : ℕ, k ≤ 1 ∧ 2 ≤ r ∧ r ≤ 7 ∧
      ((k = 0 ∧
        ∃ φ : ZMod 8 → ZMod 8,
          (∀ i j,
            (s (u i).1 = s (v j).1 ∧
              (secondOrderDefectGraph G).Adj (u i).1 (v j).1) ↔
                j = φ i) ∧
          ((∀ i, φ (i + 1) = φ i + 1) ∨
            (∀ i, φ (i + 1) = φ i - 1))) ∨
      (k = 1 ∧
        ∀ i j, s (u i).1 = s (v j).1 →
          ¬ (secondOrderDefectGraph G).Adj (u i).1 (v j).1)) := by
  classical
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  obtain ⟨_ha8, _hb8, r, hr2, hr7, _haa, _habq, _hbaq, _hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
  obtain ⟨k, hk, hA, _hB, _hcrossA, _hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
  have hu0A : u 0 ∈ A := by
    have h : u 0 ∈ a.supp := by
      rw [← hurange]
      exact ⟨0, rfl⟩
    simpa [A] using h
  have hrow : (A.filter fun y ↦ K.Adj (u 0) y ∧
      s y.1 = s (u 0).1).card = k := hA (u 0) hu0A
  refine ⟨k, r, hk, hr2, hr7, ?_⟩
  interval_cases k
  · left
    refine ⟨rfl, ?_⟩
    have hzero :
        (((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp).filter
          (fun y ↦ (secondOrderDefectGraph G).Adj (u 0).1 y.1 ∧
            s y.1 = s (u 0).1)).card = 0 := by
      simpa [A, K] using hrow
    exact orderSixtyFour_sizeTwo_muNegFive_eightEight_crossSame_orientation_of_zero
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
      u v huinj hvinj hurange hvrange hu hv 0 hzero
  · right
    refine ⟨rfl, ?_⟩
    have hone :
        (((Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp).filter
          (fun y ↦ (secondOrderDefectGraph G).Adj (u 0).1 y.1 ∧
            s y.1 = s (u 0).1)).card = 1 := by
      simpa [A, K] using hrow
    exact orderSixtyFour_sizeTwo_muNegFive_eightEight_crossSame_empty_of_one
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
      u v hurange hvrange 0 hone

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_eightEight_signed_normalForm
