import Proofs.Erdos85DegreeTwoOwnerBlockPacking

/-! # Private pairs occupy distinct owner blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two isolated `K₂,₂` row packages are disjoint when a vertex of the
second left pair is distinct from the first left pair and has no owner edge
to the first left vertex.  If the blocks were equal, that second vertex
would have to be one of the first block's two right vertices, producing the
forbidden cross edge.

The defect-private-pair application obtains the nonedge from
`equalRows_privateDefectPair_ownerCross_empty`. -/
theorem isolatedK22_blocks_disjoint_of_privateCross_nonadj
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {a b r s p q t u : V}
    (hrows₁ :
      H.neighborFinset a = {r, s} ∧
      H.neighborFinset b = {r, s} ∧
      H.neighborFinset r = {a, b} ∧
      H.neighborFinset s = {a, b})
    (hrows₂ :
      H.neighborFinset p = {t, u} ∧
      H.neighborFinset q = {t, u} ∧
      H.neighborFinset t = {p, q} ∧
      H.neighborFinset u = {p, q})
    (hpa : p ≠ a) (hpb : p ≠ b) (hnap : ¬ H.Adj a p) :
    Disjoint ({a, b, r, s} : Finset V) {p, q, t, u} := by
  rcases isolatedK22_blocks_eq_or_disjoint H
      hrows₁.1 hrows₁.2.1 hrows₁.2.2.1 hrows₁.2.2.2
      hrows₂.1 hrows₂.2.1 hrows₂.2.2.1 hrows₂.2.2.2 with heq | hdisj
  · exfalso
    have hp₂ : p ∈ ({p, q, t, u} : Finset V) := by simp
    have hp₁ : p ∈ ({a, b, r, s} : Finset V) := by
      rw [heq]
      exact hp₂
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp₁
    rcases hp₁ with h | h | h | h
    · exact hpa h
    · exact hpb h
    · apply hnap
      apply (H.mem_neighborFinset a p).mp
      rw [hrows₁.1]
      simp [h]
    · apply hnap
      apply (H.mem_neighborFinset a p).mp
      rw [hrows₁.1]
      simp [h]
  · exact hdisj

end

end Erdos85
