import Proofs.Erdos85SizeTwoEigenlineConnectedCodePackage
import Proofs.Erdos85SizeTwoEigenlineCyclicZeroSectorExclusion

/-!
# Exclusion of a connected size-two eigenline component at order 64

The coordinate-free connected package produces an exact q=8 reflection code.
The native H16 classification excludes that code for every reflection
parameter, giving the graph-facing contradiction in one theorem.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem false_of_sizeTwoEigenline_connectedInternal_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (hconn : (G.induce c.supp).Connected)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x,
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = 3 * s x) :
    False := by
  obtain ⟨a, ha, ⟨code⟩⟩ :=
    exists_nonempty_sizeTwoCyclicExactPermutationCode_of_connectedInternal
      G hfree (q := 8) (by omega) (by decide) hreg (by omega) c (by omega)
        hconn s hs_in hs_out hsum hA_in (by simpa using hDs)
  exact (sizeTwoCyclicExactPermutationCode_eight_isEmpty a).false code

end

end Erdos85

#print axioms Erdos85.false_of_sizeTwoEigenline_connectedInternal_eight
