import Proofs.Erdos85ThreeSeparatorExceptionalPointDefectNeighborhood
import Proofs.Erdos85ThreeSeparatorPositiveSpikeSmallSideLocation

/-!
# The exceptional point is not on the endpoint small shore

At `a=0`, (B16) puts at most four K-points on `X∪W`.  If the exceptional
point lay in the defect clique `X`, the rest of the clique and its two defect
attachments would all lie in K, producing at least `q` such points.  This is
the endpoint exclusion (B17'').
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Graph-facing core of (B17''): a K-contained defect neighborhood at the
center of the endpoint clique is incompatible with the B16 small-side bound. -/
theorem false_of_exceptionalPoint_mem_endpointSmallShore
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (X W K U : Finset V) (c : V) (q rX : ℕ)
    (hq8 : 8 ≤ q)
    (hXcard : X.card = q - 2)
    (hXW : Disjoint X W)
    (hcX : c ∈ X)
    (hcK : c ∈ K)
    (hclique : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → D.Adj x y)
    (hneighborK : D.neighborFinset c ⊆ K)
    (hUcard : U.card = 2)
    (hUW : U ⊆ W)
    (hUneighbor : U ⊆ D.neighborFinset c)
    (hsmall : (K ∩ (X ∪ W)).card + rX = 4) : False := by
  have hXK : X ⊆ K := by
    intro x hx
    by_cases hxc : x = c
    · simpa [hxc] using hcK
    · have hadj : D.Adj c x :=
        hclique c hcX x hx (Ne.symm hxc)
      exact hneighborK (by simpa using hadj)
  have hUK : U ⊆ K := fun _ hu ↦ hneighborK (hUneighbor hu)
  have hXU : Disjoint X U := hXW.mono_right hUW
  have hUnionCard : (X ∪ U).card = q := by
    have hc := Finset.card_union_of_disjoint hXU
    rw [hXcard, hUcard] at hc
    omega
  have hUnionSubset : X ∪ U ⊆ K ∩ (X ∪ W) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxX | hxU
    · exact Finset.mem_inter.mpr ⟨hXK hxX, Finset.mem_union_left W hxX⟩
    · exact Finset.mem_inter.mpr
        ⟨hUK hxU, Finset.mem_union_right X (hUW hxU)⟩
  have hqle : q ≤ (K ∩ (X ∪ W)).card := by
    rw [← hUnionCard]
    exact Finset.card_le_card hUnionSubset
  omega

end

end Erdos85

#print axioms Erdos85.false_of_exceptionalPoint_mem_endpointSmallShore
