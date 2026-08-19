import Proofs.Erdos85SizeTwoEigenlineReflectionCyclicAttachment

/-!
# Coordinate-free connected size-two sector package

Node: `SIZE-TWO-EIGENLINE(q)` (outline F.3).

The graph-specific cycle normalization supplies the coordinates required by
the reflection classification and attachment.  Thus the downstream cyclic
exclusion layer no longer needs a coordinate package as an input hypothesis.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A connected normalized size-two defect component canonically yields an
exact cyclic permutation code for some reflection parameter. -/
theorem exists_nonempty_sizeTwoCyclicExactPermutationCode_of_connectedInternal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hconn : (G.induce c.supp).Connected)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x) :
    ∃ a : ZMod q, a ≠ -1 ∧
      Nonempty (SizeTwoCyclicExactPermutationCode q a) := by
  obtain ⟨coord⟩ := exists_sizeTwoCycleGridCoordinates_of_connectedInternal
    G hfree q (by omega) hreg hcard c (by simpa [Nat.mul_comm] using hc)
      hconn s hs_in hs_out hA_in
  exact exists_nonempty_sizeTwoCyclicExactPermutationCode_of_connected
    G hfree hq hqEven hreg hcard c hc hconn s hs_in hs_out hsum hA_in hDs
      coord

end

end Erdos85

#print axioms Erdos85.exists_nonempty_sizeTwoCyclicExactPermutationCode_of_connectedInternal
