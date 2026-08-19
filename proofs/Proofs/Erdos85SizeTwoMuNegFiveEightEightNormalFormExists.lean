import Proofs.Erdos85SizeTwoMuNegFiveEightEightNormalForm

/-! # Coordinate-free signed normal form in the `mu=-5` C8+C8 branch -/

open Finset

namespace Erdos85

noncomputable section

set_option maxHeartbeats 1200000 in
/-- Two distinct ambient components in the `mu=-5` size-two branch admit C8
coordinates exposing the exact `k=0/1` signed cross-block dichotomy. -/
theorem orderSixtyFour_sizeTwo_muNegFive_eightEight_exists_signed_normalForm
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
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b) :
    ∃ u v : ZMod 8 → c.supp,
      Function.Injective u ∧ Function.Injective v ∧
      Set.range u = a.supp ∧ Set.range v = b.supp ∧
      (∀ z, (G.induce c.supp).neighborFinset (u z) =
        {u (z - 1), u (z + 1)}) ∧
      (∀ z, (G.induce c.supp).neighborFinset (v z) =
        {v (z - 1), v (z + 1)}) ∧
      ∃ k r : ℕ, k ≤ 1 ∧ 2 ≤ r ∧ r ≤ 7 ∧
        (((k = 0 ∧
          ∃ φ : ZMod 8 → ZMod 8,
            (∀ i j,
              (s (u i).1 = s (v j).1 ∧
                (secondOrderDefectGraph G).Adj (u i).1 (v j).1) ↔
                  j = φ i) ∧
            ((∀ i, φ (i + 1) = φ i + 1) ∨
              (∀ i, φ (i + 1) = φ i - 1))) ∨
        (k = 1 ∧
          ∀ i j, s (u i).1 = s (v j).1 →
            ¬ (secondOrderDefectGraph G).Adj (u i).1 (v j).1))) := by
  classical
  let Hc := G.induce c.supp
  obtain ⟨ha8, hb8, _r, _hr2, _hr7, _haa, _habq, _hbaq, _hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
  have hHdegree : ∀ z : c.supp, Hc.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  obtain ⟨u, v, huinj, hvinj, hurange, hvrange, hu, hv⟩ :=
    exists_zmodEight_twoComponent_coordinates Hc hHdegree a b ha8 hb8
  have hnormal :=
    orderSixtyFour_sizeTwo_muNegFive_eightEight_signed_normalForm
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
      u v huinj hvinj hurange hvrange hu hv
  exact ⟨u, v, huinj, hvinj, hurange, hvrange, hu, hv, hnormal⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_eightEight_exists_signed_normalForm

