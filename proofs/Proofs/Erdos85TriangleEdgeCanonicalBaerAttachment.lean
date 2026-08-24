import Proofs.Erdos85CanonicalBaerRelayBrokenPart

/-!
# Triangle-edge attachment to the canonical Baer relay

An ambient edge outside the triangle-free graph lies in a unique triangle.
At the third vertex it is literally the canonical triangle-partner pair.
This is the occurrence-level `rho^tri` attachment in `(73rnz_cjibku)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- An ambient edge outside `T` has a unique triangle witness, and at that
witness its endpoints form the canonical triangle-partner pair. -/
theorem existsUnique_triangleWitness_trianglePartner_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {a b : V}
    (hab : A.Adj a b) (hnotT : ¬ (triangleFreeEdgeGraph A).Adj a b) :
    ∃! r : V, A.Adj r a ∧ A.Adj r b ∧ trianglePartner A r a = b := by
  have heligAB : trianglePartnerEligible A a b :=
    (trianglePartnerEligible_iff_not_triangleFreeEdge A a b).2 ⟨hab, hnotT⟩
  let r := trianglePartner A a b
  have hrspec := trianglePartner_spec heligAB
  have hra : A.Adj r a := hrspec.1.symm
  have hrb : A.Adj r b := hrspec.2.symm
  have heligRA : trianglePartnerEligible A r a :=
    ⟨hra, b, hrb, hab⟩
  have hpartner : trianglePartner A r a = b := by
    have hs := trianglePartner_spec heligRA
    exact commonNeighbor_unique_of_c4Free hfree (A.ne_of_adj hra).symm
      hs.2 hs.1 hab hrb
  refine ⟨r, ⟨hra, hrb, hpartner⟩, ?_⟩
  intro r' hr'
  exact commonNeighbor_unique_of_c4Free hfree (A.ne_of_adj hab)
    hr'.1.symm hr'.2.1.symm hra.symm hrb.symm

/-- Consequently every triangle edge is present as a canonical `00` edge
of any completed full Baer relay. -/
theorem triangleEdge_fullCanonicalBaerRelay_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (mate : V → V → V)
    (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
    (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
    (hfixed : ∀ p x, A.Adj p x → mate p x ≠ x)
    (hcanonical : ∀ p x, trianglePartnerEligible A p x →
      mate p x = trianglePartner A p x)
    {a b : V} (hab : A.Adj a b)
    (hnotT : ¬ (triangleFreeEdgeGraph A).Adj a b) :
    (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed).Adj a b := by
  obtain ⟨r, hr, _⟩ :=
    existsUnique_triangleWitness_trianglePartner_eq A hfree hab hnotT
  change ∃ r, A.Adj r a ∧ mate r a = b
  refine ⟨r, hr.1, ?_⟩
  rw [hcanonical r a ⟨hr.1, b, hr.2.1, hab⟩]
  exact hr.2.2

end

end Erdos85

#print axioms Erdos85.existsUnique_triangleWitness_trianglePartner_eq
#print axioms Erdos85.triangleEdge_fullCanonicalBaerRelay_adj
