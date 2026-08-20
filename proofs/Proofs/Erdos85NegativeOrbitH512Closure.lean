import Proofs.Erdos85MuNegFiveOneTwoCrossOnlyTerminal
import Proofs.Erdos85NegativeOrbitSignedJointClosure

/-! # Post-h512 negative-orbit closure

The corrected h512 graph callback imports the base orbit assembly, so this
thin downstream module consumes it without creating an import cycle.  The
only remaining canonical negative endpoint is h305.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem false_of_negativeEightEightSource_of_h305
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (theta : ℤ) (k r : ℕ) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    NegativeEightEightSourceWitness G c a b N₁ N₂ theta k r →
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 0 5) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 0 5 → False) →
    False := by
  dsimp only
  intro w h305
  exact false_of_negativeEightEightSource_of_two_canonicalTerminals
    G hfree hreg hcard c hc a b hab u v huinj hvinj hurange hvrange hu hv
      theta k r w
      (false_of_h512_source_or_transported G hfree hreg hcard c hc
        a b hab u v huinj hvinj hurange hvrange hu hv)
      h305

/-- After the corrected h512 callback, every normalized 8+8 signed joint is
impossible from the single residual h305 endpoint callback. -/
theorem orderSixtyFour_regular_sizeTwo_signedJoint_false_of_h305
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
    (Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 0 5) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 0 5 → False) →
    False := by
  dsimp only
  intro h305
  apply orderSixtyFour_regular_sizeTwo_signedJoint_false_of_h512_h305
    G hfree hreg c hc s mu hs_out hs_in hH hD x hx
      a b hab u v huinj hvinj hurange hvrange hu hv
  · exact false_of_h512_source_or_transported G hfree hreg (by norm_num)
      c (by simpa using hc) a b hab u v huinj hvinj hurange hvrange hu hv
  · exact h305

end

end Erdos85

#print axioms Erdos85.false_of_negativeEightEightSource_of_h305
#print axioms Erdos85.orderSixtyFour_regular_sizeTwo_signedJoint_false_of_h305
