import Proofs.Erdos85DisjointFiberMateAssembly
import Proofs.Erdos85C4FreeWitnessPairingRelay

/-!
# Canonical completed Baer relay

This composes the canonical triangle-partner completion with the global
witness-indexed relay construction.  Unlike the arbitrary paired-star
existence theorem, the resulting mate is definitionally constrained to agree
with the canonical partial Baer involution on every non-broken endpoint.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A C4-free regular graph with even broken fibers admits a canonical
completed neighbor-star relay.  The relay is `q`-regular and Eulerian, while
all non-broken local pairs remain the canonical triangle-partner pairs. -/
theorem exists_canonicalBaer_neighborStar_relay
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A) (q : ℕ)
    (hreg : ∀ v, A.degree v = q) (hq : Even q)
    (hevenBroken : ∀ p, Even ((Finset.univ.filter fun x =>
      (triangleFreeEdgeGraph A).Adj p x).card)) :
    ∃ (mate : V → V → V)
      (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
      (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
      (hfixed : ∀ p x, A.Adj p x → mate p x ≠ x),
      (∀ p x, trianglePartnerEligible A p x →
        mate p x = trianglePartner A p x) ∧
      (∀ v, (witnessPairingRelayGraph A.Adj mate
        hclosed hinvol hfixed).degree v = q) ∧
      (∀ v, Even ((witnessPairingRelayGraph A.Adj mate
        hclosed hinvol hfixed).degree v)) := by
  obtain ⟨mate, hclosed, hinvol, hfixed, hcanonical⟩ :=
    exists_baerCompletedMate_of_even_brokenFibers A hfree hevenBroken
  refine ⟨mate, hclosed, hinvol, hfixed, hcanonical, ?_, ?_⟩
  · intro v
    exact c4Free_neighborStar_relay_degree_eq A hfree mate
      hclosed hinvol hfixed q hreg v
  · intro v
    exact c4Free_neighborStar_relay_even_degree A hfree mate
      hclosed hinvol hfixed q hreg hq v

end

end Erdos85

#print axioms Erdos85.exists_canonicalBaer_neighborStar_relay
