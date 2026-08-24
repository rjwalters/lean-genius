import Proofs.Erdos85CanonicalBaerRelayExists
import Proofs.Erdos85BrokenFiberParity

/-!
# Canonical Baer relay from even regularity alone

The broken-fiber parity theorem removes the last extra local hypothesis from
the canonical relay construction.  Even regularity and C4-freeness now
construct the completed canonical mate family and its Eulerian relay directly.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every finite C4-free even-regular graph admits the canonical completed
neighbor-star relay, with no separately assumed broken-fiber parity. -/
theorem exists_canonicalBaer_neighborStar_relay_of_evenRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A) (q : ℕ)
    (hreg : ∀ v, A.degree v = q) (hq : Even q) :
    ∃ (mate : V → V → V)
      (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
      (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
      (hfixed : ∀ p x, A.Adj p x → mate p x ≠ x),
      (∀ p x, trianglePartnerEligible A p x →
        mate p x = trianglePartner A p x) ∧
      (∀ v, (witnessPairingRelayGraph A.Adj mate
        hclosed hinvol hfixed).degree v = q) ∧
      ∀ v, Even ((witnessPairingRelayGraph A.Adj mate
        hclosed hinvol hfixed).degree v) := by
  apply exists_canonicalBaer_neighborStar_relay A hfree q hreg hq
  intro p
  apply even_triangleFreeEdge_fiber_of_even_degree A hfree p
  simpa [hreg p] using hq

#print axioms exists_canonicalBaer_neighborStar_relay_of_evenRegular

end

end Erdos85
