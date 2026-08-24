import Proofs.Erdos85DisjointFiberMateAssembly
import Proofs.Erdos85BrokenFiberParity
import Proofs.Erdos85PrescribedPairInvolution
import Proofs.Erdos85C4FreeWitnessPairingRelay

/-!
# Owner-prescribed canonical Baer mate family

Given one named broken pair at every witness, construct the full local mate
family simultaneously: canonical triangle pairs remain fixed and every named
broken pair is realized.  This is the graph-facing owner-normal-form adapter.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Even regularity supplies canonical completed local mates realizing any
prescribed distinct broken pair at every witness. -/
theorem exists_partiallyOwnerPrescribed_baerCompletedMate
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A) (q : ℕ)
    (hreg : ∀ p, A.degree p = q) (hq : Even q)
    (owner : V → Prop) (a b : V → V)
    (hab : ∀ p, owner p → a p ≠ b p)
    (haBroken : ∀ p, owner p → (triangleFreeEdgeGraph A).Adj p (a p))
    (hbBroken : ∀ p, owner p → (triangleFreeEdgeGraph A).Adj p (b p)) :
    ∃ mate : V → V → V,
      (∀ p x, A.Adj p x → A.Adj p (mate p x)) ∧
      (∀ p x, A.Adj p x → mate p (mate p x) = x) ∧
      (∀ p x, A.Adj p x → mate p x ≠ x) ∧
      (∀ p x, trianglePartnerEligible A p x →
        mate p x = trianglePartner A p x) ∧
      ∀ p, owner p → mate p (a p) = b p ∧ mate p (b p) = a p := by
  let broken : V → Finset V := fun p =>
    Finset.univ.filter fun x => (triangleFreeEdgeGraph A).Adj p x
  have hevenBroken : ∀ p, Even (broken p).card := by
    intro p
    apply even_triangleFreeEdge_fiber_of_even_degree A hfree p
    simpa [hreg p] using hq
  have hexists : ∀ p, ∃ right : V → V,
      (owner p → right (a p) = b p ∧ right (b p) = a p) ∧
      (∀ x, x ∈ broken p → right x ∈ broken p) ∧
      (∀ x, x ∈ broken p → right (right x) = x) ∧
      (∀ x, x ∈ broken p → right x ≠ x) := by
    intro p
    by_cases hp : owner p
    · obtain ⟨right, hra, hrb, hclosed, hinvol, hfixed, _⟩ :=
        exists_mate_of_even_finset_with_prescribed_pair
          (broken p) (a p) (b p) (hevenBroken p) (hab p hp)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, haBroken p hp⟩)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbBroken p hp⟩)
      exact ⟨right, fun _ => ⟨hra, hrb⟩, hclosed, hinvol, hfixed⟩
    · obtain ⟨right, hclosed, hinvol, hfixed, _⟩ :=
        exists_mate_of_even_finset (broken p) (hevenBroken p)
      exact ⟨right, fun hp' => False.elim (hp hp'), hclosed, hinvol, hfixed⟩
  choose right hprescribed hrightClosed hrightInvol hrightFixed using hexists
  let mate : V → V → V := fun p =>
    disjointFiberMate (trianglePartnerEligible A p)
      (trianglePartner A p) (right p)
  have hcover : ∀ p x, A.Adj p x →
      trianglePartnerEligible A p x ∨
        (triangleFreeEdgeGraph A).Adj p x := by
    intro p x hpx
    by_cases helig : trianglePartnerEligible A p x
    · exact Or.inl helig
    · exact Or.inr <| by
        by_contra hbroken
        exact helig ((trianglePartnerEligible_iff_not_triangleFreeEdge A p x).2
          ⟨hpx, hbroken⟩)
  have hprops : ∀ p,
      (∀ x, trianglePartnerEligible A p x ∨
          (triangleFreeEdgeGraph A).Adj p x →
        trianglePartnerEligible A p (mate p x) ∨
          (triangleFreeEdgeGraph A).Adj p (mate p x)) ∧
      (∀ x, trianglePartnerEligible A p x ∨
          (triangleFreeEdgeGraph A).Adj p x → mate p (mate p x) = x) ∧
      ∀ x, trianglePartnerEligible A p x ∨
          (triangleFreeEdgeGraph A).Adj p x → mate p x ≠ x := by
    intro p
    apply disjointFiberMate_properties
    · intro x helig
      exact ((trianglePartnerEligible_iff_not_triangleFreeEdge A p x).1 helig).2
    · exact fun x hx => trianglePartner_closed hx
    · exact fun x hx => trianglePartner_involutive hfree hx
    · exact fun x hx => trianglePartner_fixedPointFree hx
    · intro x hx
      have hx' : x ∈ broken p :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      have hm := hrightClosed p x hx'
      exact (Finset.mem_filter.mp hm).2
    · intro x hx
      exact hrightInvol p x
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
    · intro x hx
      exact hrightFixed p x
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
  refine ⟨mate, ?_, ?_, ?_, ?_, ?_⟩
  · intro p x hpx
    rcases (hprops p).1 x (hcover p x hpx) with helig | hbroken
    · exact ((trianglePartnerEligible_iff_not_triangleFreeEdge A p (mate p x)).1
        helig).1
    · exact ((mem_triangleFreeNeighbors A p (mate p x)).mp
        ((triangleFreeEdgeGraph_adj A p (mate p x)).mp hbroken)).1
  · intro p x hpx
    exact (hprops p).2.1 x (hcover p x hpx)
  · intro p x hpx
    exact (hprops p).2.2 x (hcover p x hpx)
  · intro p x helig
    simp [mate, disjointFiberMate, helig]
  · intro p hp
    have hpairs := hprescribed p hp
    have haNotEligible : ¬ trianglePartnerEligible A p (a p) := by
      intro helig
      exact ((trianglePartnerEligible_iff_not_triangleFreeEdge A p (a p)).1
        helig).2 (haBroken p hp)
    have hbNotEligible : ¬ trianglePartnerEligible A p (b p) := by
      intro helig
      exact ((trianglePartnerEligible_iff_not_triangleFreeEdge A p (b p)).1
        helig).2 (hbBroken p hp)
    exact ⟨by simp [mate, disjointFiberMate, haNotEligible, hpairs.1],
      by simp [mate, disjointFiberMate, hbNotEligible, hpairs.2]⟩

/-- Full-support specialization: prescribe a broken pair at every witness. -/
theorem exists_ownerPrescribed_baerCompletedMate
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A) (q : ℕ)
    (hreg : ∀ p, A.degree p = q) (hq : Even q)
    (a b : V → V) (hab : ∀ p, a p ≠ b p)
    (haBroken : ∀ p, (triangleFreeEdgeGraph A).Adj p (a p))
    (hbBroken : ∀ p, (triangleFreeEdgeGraph A).Adj p (b p)) :
    ∃ mate : V → V → V,
      (∀ p x, A.Adj p x → A.Adj p (mate p x)) ∧
      (∀ p x, A.Adj p x → mate p (mate p x) = x) ∧
      (∀ p x, A.Adj p x → mate p x ≠ x) ∧
      (∀ p x, trianglePartnerEligible A p x →
        mate p x = trianglePartner A p x) ∧
      ∀ p, mate p (a p) = b p ∧ mate p (b p) = a p := by
  obtain ⟨mate, hclosed, hinvol, hfixed, hcanonical, hprescribed⟩ :=
    exists_partiallyOwnerPrescribed_baerCompletedMate A hfree q hreg hq
      (fun _ => True) a b (fun p _ => hab p)
      (fun p _ => haBroken p) (fun p _ => hbBroken p)
  exact ⟨mate, hclosed, hinvol, hfixed, hcanonical,
    fun p => hprescribed p trivial⟩

/-- The owner-prescribed mate family produces the same exact q-regular
Eulerian global relay as the arbitrary canonical completion. -/
theorem exists_partiallyOwnerPrescribed_canonicalBaer_relay
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A) (q : ℕ)
    (hreg : ∀ p, A.degree p = q) (hq : Even q)
    (owner : V → Prop) (a b : V → V)
    (hab : ∀ p, owner p → a p ≠ b p)
    (haBroken : ∀ p, owner p → (triangleFreeEdgeGraph A).Adj p (a p))
    (hbBroken : ∀ p, owner p → (triangleFreeEdgeGraph A).Adj p (b p)) :
    ∃ (mate : V → V → V)
      (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
      (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
      (hfixed : ∀ p x, A.Adj p x → mate p x ≠ x),
      (∀ p x, trianglePartnerEligible A p x →
        mate p x = trianglePartner A p x) ∧
      (∀ p, owner p → mate p (a p) = b p ∧ mate p (b p) = a p) ∧
      (∀ v, (witnessPairingRelayGraph A.Adj mate
        hclosed hinvol hfixed).degree v = q) ∧
      ∀ v, Even ((witnessPairingRelayGraph A.Adj mate
        hclosed hinvol hfixed).degree v) := by
  obtain ⟨mate, hclosed, hinvol, hfixed, hcanonical, hprescribed⟩ :=
    exists_partiallyOwnerPrescribed_baerCompletedMate
      A hfree q hreg hq owner a b hab haBroken hbBroken
  refine ⟨mate, hclosed, hinvol, hfixed, hcanonical, hprescribed, ?_, ?_⟩
  · intro v
    exact c4Free_neighborStar_relay_degree_eq A hfree mate
      hclosed hinvol hfixed q hreg v
  · intro v
    exact c4Free_neighborStar_relay_even_degree A hfree mate
      hclosed hinvol hfixed q hreg hq v

/-- Full-support owner-prescribed relay specialization. -/
theorem exists_ownerPrescribed_canonicalBaer_relay
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A) (q : ℕ)
    (hreg : ∀ p, A.degree p = q) (hq : Even q)
    (a b : V → V) (hab : ∀ p, a p ≠ b p)
    (haBroken : ∀ p, (triangleFreeEdgeGraph A).Adj p (a p))
    (hbBroken : ∀ p, (triangleFreeEdgeGraph A).Adj p (b p)) :
    ∃ (mate : V → V → V)
      (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
      (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
      (hfixed : ∀ p x, A.Adj p x → mate p x ≠ x),
      (∀ p x, trianglePartnerEligible A p x →
        mate p x = trianglePartner A p x) ∧
      (∀ p, mate p (a p) = b p ∧ mate p (b p) = a p) ∧
      (∀ v, (witnessPairingRelayGraph A.Adj mate
        hclosed hinvol hfixed).degree v = q) ∧
      ∀ v, Even ((witnessPairingRelayGraph A.Adj mate
        hclosed hinvol hfixed).degree v) := by
  obtain ⟨mate, hclosed, hinvol, hfixed, hcanonical, hprescribed⟩ :=
    exists_ownerPrescribed_baerCompletedMate
      A hfree q hreg hq a b hab haBroken hbBroken
  refine ⟨mate, hclosed, hinvol, hfixed, hcanonical, hprescribed, ?_, ?_⟩
  · intro v
    exact c4Free_neighborStar_relay_degree_eq A hfree mate
      hclosed hinvol hfixed q hreg v
  · intro v
    exact c4Free_neighborStar_relay_even_degree A hfree mate
      hclosed hinvol hfixed q hreg hq v

#print axioms exists_partiallyOwnerPrescribed_baerCompletedMate
#print axioms exists_ownerPrescribed_baerCompletedMate
#print axioms exists_partiallyOwnerPrescribed_canonicalBaer_relay
#print axioms exists_ownerPrescribed_canonicalBaer_relay

end

end Erdos85
