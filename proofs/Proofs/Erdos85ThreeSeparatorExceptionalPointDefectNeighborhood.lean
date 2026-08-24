import Proofs.Erdos85ThreeSeparatorExceptionalPointMatching

/-!
# Exact exceptional-point defect neighborhood

After the exceptional-point matching identifies `q` K-points that are
defect-nonneighbors of `c`, degree saturation identifies every remaining
K-point (apart from `c`) as a defect neighbor.  This is (B17').
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Generic saturation form of (B17'). -/
theorem neighborFinset_eq_cover_sdiff_center_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (K Q : Finset V) (c : V) (q : ℕ)
    (hq : 1 ≤ q)
    (hcK : c ∈ K)
    (hQK : Q ⊆ K)
    (hcQ : c ∉ Q)
    (hKcard : K.card = 2 * q)
    (hQcard : Q.card = q)
    (hdegree : D.degree c = q - 1)
    (hsubset : D.neighborFinset c ⊆ K \ insert c Q) :
    D.neighborFinset c = K \ insert c Q := by
  have hinsertSubset : insert c Q ⊆ K := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hcK
    · exact hQK hx
  have hinsertCard : (insert c Q).card = q + 1 := by
    rw [Finset.card_insert_of_notMem hcQ, hQcard]
  have htargetCard : (K \ insert c Q).card = q - 1 := by
    rw [Finset.card_sdiff_of_subset hinsertSubset, hKcard, hinsertCard]
    omega
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [D.card_neighborFinset_eq_degree, hdegree, htargetCard]

end

end Erdos85

#print axioms Erdos85.neighborFinset_eq_cover_sdiff_center_image
