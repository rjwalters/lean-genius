import Proofs.Erdos85SizeTwoEigenlineConnectedEightExclusion
import Proofs.Erdos85SizeTwoEigenlineDisconnectedTerminalAssembly

/-!
# Terminal assembly for an order-64 size-two eigenline component

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The internal graph on the sixteen supported vertices is either connected, in
which case the cyclic-code classification is contradictory, or it has two
distinct connected components, which are passed to the disconnected terminal.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The connected/disconnected top-level split for a normalized q=8 size-two
eigenline component.  The only remaining input is the graph-facing terminal
for a pair of distinct internal connected components. -/
theorem false_of_sizeTwoEigenline_eight_of_disconnected_terminal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((8 : ℤ) - 5) * s x)
    (hDisconnected : ∀ a b : (G.induce c.supp).ConnectedComponent,
      a ≠ b → False) :
    False := by
  let H := G.induce c.supp
  by_cases hconn : H.Connected
  · exact false_of_connected_sizeTwoEigenline_eight
      G hfree hreg hcard c hc hconn s hs_in hs_out hsum hA_in hDs
  · rw [H.connected_iff_exists_forall_reachable] at hconn
    push_neg at hconn
    have hsupp : c.supp.Nonempty := (Set.ncard_pos).mp (by omega)
    obtain ⟨x, hx⟩ := hsupp
    let xs : c.supp := ⟨x, hx⟩
    obtain ⟨ys, hxys⟩ := hconn xs
    let a := H.connectedComponentMk xs
    let b := H.connectedComponentMk ys
    have hab : a ≠ b := by
      intro hab
      exact hxys (ConnectedComponent.exact hab)
    exact hDisconnected a b hab

end

end Erdos85

#print axioms Erdos85.false_of_sizeTwoEigenline_eight_of_disconnected_terminal
