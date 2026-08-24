import Proofs.Erdos85TriangleEdgeCanonicalBaerAttachment

/-!
# Cut attachment dichotomy for flipping ambient edges

A vertex-cut crossing carried by an ambient edge belongs to exactly one of
the two containers in `(73rnz_cjibkw)`: a triangle-free edge lies in the
`T` cut, while a triangle edge is a canonical `00` edge of the full Baer
relay and lies in its cut.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A triangle-free ambient edge cannot itself be an edge of a neighbor-star
relay: a relay witness would be a common neighbor of its endpoints. -/
theorem triangleFreeEdge_not_witnessPairingRelayGraph_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (mate : V → V → V)
    (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
    (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
    (hfixed : ∀ p x, A.Adj p x → mate p x ≠ x)
    {a b : V} (hT : (triangleFreeEdgeGraph A).Adj a b) :
    ¬ (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed).Adj a b := by
  intro hP
  change ∃ w, A.Adj w a ∧ mate w a = b at hP
  obtain ⟨w, hwa, hm⟩ := hP
  have hwb : A.Adj w b := by
    rw [← hm]
    exact hclosed w a hwa
  have hw : w ∈ A.neighborFinset a ∩ A.neighborFinset b := by
    exact Finset.mem_inter.mpr ⟨
      (A.mem_neighborFinset a w).mpr hwa.symm,
      (A.mem_neighborFinset b w).mpr hwb.symm⟩
  have hzero := ((mem_triangleFreeNeighbors A a b).mp hT).2
  have hempty : A.neighborFinset a ∩ A.neighborFinset b = ∅ :=
    Finset.card_eq_zero.mp hzero
  rw [hempty] at hw
  exact (by simpa using hw)

/-- **Flipping ambient-edge attachment (73rnz_cjibkw).**  An ambient edge
crossing `B` lies in exactly one of the `T` cut and the canonical full-relay
cut. -/
theorem ambientEdge_flip_attaches_to_exactly_one_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (mate : V → V → V)
    (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
    (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
    (hfixed : ∀ p x, A.Adj p x → mate p x ≠ x)
    (hcanonical : ∀ p x, trianglePartnerEligible A p x →
      mate p x = trianglePartner A p x)
    (B : Finset V) {a b : V} (hab : A.Adj a b)
    (hflip : (a ∈ B) ≠ (b ∈ B)) :
    ((binaryVertexCutGraph (triangleFreeEdgeGraph A) B).Adj a b ∧
      ¬ (binaryVertexCutGraph
        (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed) B).Adj a b) ∨
    ((binaryVertexCutGraph
        (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed) B).Adj a b ∧
      ¬ (binaryVertexCutGraph (triangleFreeEdgeGraph A) B).Adj a b) := by
  by_cases hT : (triangleFreeEdgeGraph A).Adj a b
  · left
    exact ⟨⟨hT, hflip⟩, fun hP =>
      triangleFreeEdge_not_witnessPairingRelayGraph_adj
        A mate hclosed hinvol hfixed hT hP.1⟩
  · right
    have hP := triangleEdge_fullCanonicalBaerRelay_adj
      A hfree mate hclosed hinvol hfixed hcanonical hab hT
    exact ⟨⟨hP, hflip⟩, fun hcut => hT hcut.1⟩

end

end Erdos85

#print axioms Erdos85.triangleFreeEdge_not_witnessPairingRelayGraph_adj
#print axioms Erdos85.ambientEdge_flip_attaches_to_exactly_one_cut
