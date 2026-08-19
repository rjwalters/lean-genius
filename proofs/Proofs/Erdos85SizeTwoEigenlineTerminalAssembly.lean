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

/-- Fully structural top-level assembly: after the connected branch has been
excluded, the disconnected reduction leaves only the oriented `6+10` and
symmetric `8+8` quotient strata. -/
theorem false_of_sizeTwoEigenline_eight_of_stratum_terminals
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
    (hSixTen : ∀ (a b : (G.induce c.supp).ConnectedComponent), a ≠ b →
      (a.supp.ncard = 6 ∧ b.supp.ncard = 10 ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 2 ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 5 ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 3 ∧
        componentQuotientMatrix
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 4) →
      False)
    (hEightEight : ∀ (a b : (G.induce c.supp).ConnectedComponent), a ≠ b →
      (a.supp.ncard = 8 ∧ b.supp.ncard = 8 ∧
        ∃ r : ℕ, 2 ≤ r ∧ r ≤ 7 ∧
          componentQuotientMatrix
              ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 7 - r ∧
          componentQuotientMatrix
              ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = r ∧
          componentQuotientMatrix
              ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = r ∧
          componentQuotientMatrix
              ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 7 - r) →
      False) :
    False := by
  apply false_of_sizeTwoEigenline_eight_of_disconnected_terminal
      G hfree hreg hcard c hc s hs_in hs_out hsum hA_in hDs
  intro a b hab
  exact binarySquare_regular_sizeTwoPart_eight_disconnected_false_of_terminals
    G hfree hreg hcard c hc s hs_in hs_out hA_in a b hab hSixTen
      (hEightEight a b hab)

end

end Erdos85

#print axioms Erdos85.false_of_sizeTwoEigenline_eight_of_disconnected_terminal
#print axioms Erdos85.false_of_sizeTwoEigenline_eight_of_stratum_terminals
