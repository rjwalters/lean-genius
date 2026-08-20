import Proofs.Erdos85NegativeSignedJointDisconnectedClosure

/-! # Full negative signed-joint structural split

This is the exact parent socket of the disconnected normalization: every
regular order-64 negative signed joint is reduced either to the connected
internal `C16` frontier or to the single `h305` graph callback.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem orderSixtyFour_regular_sizeTwo_signedJoint_false_of_connected_of_h305
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
    (hconnected : (G.induce c.supp).Connected → False)
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
  let H := G.induce c.supp
  by_cases hconn : H.Connected
  · exact hconnected hconn
  · rw [H.connected_iff_exists_forall_reachable] at hconn
    push_neg at hconn
    have hsupp : c.supp.Nonempty := (Set.ncard_pos).mp (by omega)
    obtain ⟨x₀, hx₀⟩ := hsupp
    let xs : c.supp := ⟨x₀, hx₀⟩
    obtain ⟨ys, hxys⟩ := hconn xs
    let a := H.connectedComponentMk xs
    let b := H.connectedComponentMk ys
    have hab : a ≠ b := by
      intro hab
      exact hxys (ConnectedComponent.exact hab)
    exact orderSixtyFour_regular_sizeTwo_signedJoint_disconnected_false_of_h305
      G hfree hreg c hc s mu hs_out hs_in hH hD x hx a b hab h305

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_sizeTwo_signedJoint_false_of_connected_of_h305
