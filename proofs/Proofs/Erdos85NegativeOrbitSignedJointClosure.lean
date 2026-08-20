import Proofs.Erdos85NegativeOrbitAssembly
import Proofs.Erdos85RegularSignedJointSplit

/-! # Signed-joint consumer of the negative eight-plus-eight orbit closure -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Once h512 and h305 are excluded, every signed joint on the normalized
eight-plus-eight component is impossible.  The other negative eigenvalues
and every other canonical endpoint are discharged internally. -/
theorem orderSixtyFour_regular_sizeTwo_signedJoint_false_of_h512_h305
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
    (hother : ∀ c' : (secondOrderDefectGraph G).ConnectedComponent,
      c' ≠ c → c'.supp.ncard ≠ 8)
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
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-5) 1 2) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-5) 1 2 → False) →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 0 5) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 0 5 → False) →
    False := by
  classical
  dsimp only
  let K := (secondOrderDefectGraph G).induce c.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  intro h512 h305
  apply orderSixtyFour_regular_sizeTwo_signedJoint_false_of_three_negative_cases
    G hfree hreg c hc s mu hs_out hs_in hH hD x hx
  · intro hmu
    subst mu
    letI : DecidableRel (MuNegFiveNeutralProjection G c s) :=
      fun _ _ ↦ Classical.propDecidable _
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
    obtain ⟨k, r, w⟩ := exists_negativeEightEightSource_muNegFive
      G hfree hreg (by norm_num) c (by simpa using hc) s
        hs_out hs_in hA_in hH (by simpa using hD)
        a b hab u v huinj hvinj hurange hvrange hu hv
    rcases w with ⟨w⟩
    exact false_of_negativeEightEightSource_of_two_canonicalTerminals
      G hfree hreg (by norm_num) c (by simpa using hc)
        a b hab u v huinj hvinj hurange hvrange hu hv (-5) k r
        w h512 h305
  · intro hmu
    subst mu
    obtain ⟨k, r, w⟩ := exists_negativeEightEightSource_muNegThree
      G hfree hreg (by norm_num) c (by simpa using hc) s hs_out hs_in hH
        (by simpa using hD) a b hab u v huinj hvinj hurange hvrange hu hv
    rcases w with ⟨w⟩
    exact false_of_negativeEightEightSource_of_two_canonicalTerminals
      G hfree hreg (by norm_num) c (by simpa using hc)
        a b hab u v huinj hvinj hurange hvrange hu hv (-3) k r
        w h512 h305
  · intro hmu
    subst mu
    obtain ⟨k, r, w⟩ := exists_negativeEightEightSource_muNegOne
      G hfree hreg (by norm_num) c (by simpa using hc) hother s
        hs_out hs_in hH (by simpa using hD)
        a b hab u v huinj hvinj hurange hvrange hu hv
    rcases w with ⟨w⟩
    exact false_of_negativeEightEightSource_of_two_canonicalTerminals
      G hfree hreg (by norm_num) c (by simpa using hc)
        a b hab u v huinj hvinj hurange hvrange hu hv (-1) k r
        w h512 h305

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_sizeTwo_signedJoint_false_of_h512_h305
