import Proofs.Erdos85NegativeOrbitH512Closure
import Proofs.Erdos85SizeTwoEigenlineDisconnectedEightReduction
import Proofs.Erdos85EightEightNormalizedCoordinates
import Proofs.Erdos85SizeTwoMuNegFiveSixTenTerminal
import Proofs.Erdos85SizeTwoMuNegThreeSixTenExclusion
import Proofs.Erdos85SizeTwoMuNegOneSixTenExclusion

/-! # Disconnected negative signed-joint normalization

An arbitrary disconnected internal two-factor at order 64 has cycle type
`6+10`, `10+6`, or `8+8`.  The first two types are already impossible for
all surviving negative defect eigenvalues.  This file constructs the cycle
coordinates in the last type and connects the abstract disconnected branch
to the normalized negative-orbit terminal.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Every disconnected order-64 size-two signed joint reduces to the
normalized `8+8` h305 callback.  The `6+10` orientations and all other
eigenvalue modes are discharged internally. -/
theorem orderSixtyFour_regular_sizeTwo_signedJoint_disconnected_false_of_h305
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 16)
    (s : Fin 64 → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z)
    (x : Fin 64) (hx : x ∈ c.supp)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (h305 : ∀
      (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
      (u v : ZMod 8 → c.supp)
      (huinj : Function.Injective u) (hvinj : Function.Injective v)
      (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
      (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
        {u (z - 1), u (z + 1)})
      (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
        {v (z - 1), v (z + 1)}),
      let K := (secondOrderDefectGraph G).induce c.supp
      let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
        fun i j ↦ K.adjMatrix ℤ (u i) (u j)
      let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
        fun i j ↦ K.adjMatrix ℤ (v i) (v j)
      Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 0 5) ∨
        NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 0 5 → False) :
    False := by
  classical
  have hcard : Fintype.card (Fin 64) = 8 * 8 := by norm_num
  have hA_in : ∀ z ∈ c.supp,
      ∑ y ∈ G.neighborFinset z, s y = -2 * s z := by
    intro z hz
    rw [← hH z hz]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro y hy hyout
    have hyc : y ∉ c.supp := by
      intro hyin
      apply hyout
      exact Finset.mem_filter.mpr ⟨hy,
        (ConnectedComponent.mem_supp_iff c y).mp hyin⟩
    simp [hs_out y hyc]
  rcases binarySquare_regular_sizeTwoPart_eight_disconnected_cycleQuotient_reduction
      G hfree hreg hcard c (by simpa using hc) s hs_in hs_out hA_in a b hab with
    h610 | h106 | h88
  · obtain ⟨ha, hb, _⟩ := h610
    apply orderSixtyFour_regular_sizeTwo_signedJoint_false_of_three_negative_cases
      G hfree hreg c hc s mu hs_out hs_in hH hD x hx
    · intro hmu
      subst mu
      letI : DecidableRel (MuNegFiveNeutralProjection G c s) :=
        fun _ _ ↦ Classical.propDecidable _
      exact orderSixtyFour_sizeTwo_muNegFive_sixTen_false
        G hfree hreg hcard c (by simpa using hc) s hs_out hs_in hA_in hH
          (by simpa using hD) a b hab ha hb
    · intro hmu
      subst mu
      exact orderSixtyFour_sizeTwo_muNegThree_sixTen_false
        G hfree hreg hcard c (by simpa using hc) s hs_out hs_in hH
          (by simpa using hD) a b ha hb
    · intro hmu
      subst mu
      exact orderSixtyFour_sizeTwo_muNegOne_sixTen_false
        G hfree hreg hcard c (by simpa using hc) s hs_out hs_in hH
          (by simpa using hD) a b ha hb
  · obtain ⟨ha, hb, _⟩ := h106
    apply orderSixtyFour_regular_sizeTwo_signedJoint_false_of_three_negative_cases
      G hfree hreg c hc s mu hs_out hs_in hH hD x hx
    · intro hmu
      subst mu
      letI : DecidableRel (MuNegFiveNeutralProjection G c s) :=
        fun _ _ ↦ Classical.propDecidable _
      exact orderSixtyFour_sizeTwo_muNegFive_sixTen_false
        G hfree hreg hcard c (by simpa using hc) s hs_out hs_in hA_in hH
          (by simpa using hD) b a hab.symm hb ha
    · intro hmu
      subst mu
      exact orderSixtyFour_sizeTwo_muNegThree_sixTen_false
        G hfree hreg hcard c (by simpa using hc) s hs_out hs_in hH
          (by simpa using hD) b a hb ha
    · intro hmu
      subst mu
      exact orderSixtyFour_sizeTwo_muNegOne_sixTen_false
        G hfree hreg hcard c (by simpa using hc) s hs_out hs_in hH
          (by simpa using hD) b a hb ha
  · obtain ⟨ha, hb, _⟩ := h88
    let H := G.induce c.supp
    have hdeg : ∀ z : c.supp, H.degree z = 2 := by
      intro z
      exact binarySquare_regular_degree_induce_defectComponent_eq_part
        G hfree (by omega) hreg hcard c (m := 2) (by simpa using hc) z
    obtain ⟨u, v, huinj, hvinj, hurange, hvrange, hu, hv⟩ :=
      exists_zmodEight_twoComponent_coordinates H hdeg a b ha hb
    exact orderSixtyFour_regular_sizeTwo_signedJoint_false_of_h305
      G hfree hreg c hc s mu hs_out hs_in hH hD x hx
        a b hab u v huinj hvinj hurange hvrange hu hv
        (h305 a b hab u v huinj hvinj hurange hvrange hu hv)

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_sizeTwo_signedJoint_disconnected_false_of_h305
