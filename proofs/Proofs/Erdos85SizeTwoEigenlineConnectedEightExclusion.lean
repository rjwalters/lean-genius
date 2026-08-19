import Proofs.Erdos85SizeTwoEigenlineConnectedCodePackage
import Proofs.Erdos85SizeTwoEigenlineCyclicZeroSectorExclusion

/-!
# Connected q=8 size-two eigenline exclusion

The q-generic connected-component package constructs an exact cyclic code at
some reflection parameter.  The native q=8 classification excludes that code
for every parameter, giving the graph-facing contradiction for the entire
connected normalized size-two branch.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- No connected normalized size-two eigenline component with the stated
q=8 square-order laws can occur. -/
theorem false_of_connected_sizeTwoEigenline_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (hconn : (G.induce c.supp).Connected)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((8 : ℤ) - 5) * s x) : False := by
  obtain ⟨a, _ha, ⟨code⟩⟩ :=
    exists_nonempty_sizeTwoCyclicExactPermutationCode_of_connectedInternal
      G hfree (q := 8) (by omega) (by decide) hreg hcard c hc hconn s
        hs_in hs_out hsum hA_in hDs
  exact (sizeTwoCyclicExactPermutationCode_eight_isEmpty a).false code

end

end Erdos85

#print axioms Erdos85.false_of_connected_sizeTwoEigenline_eight
