import Proofs.Erdos85CanonicalBaerRelayResidualPrice
import Proofs.Erdos85DisconnectedEulerianOddResidualHolonomy
import Proofs.Erdos85OddWeightCycleExtraction

/-!
# Global odd-cycle or potential alternative

No connectivity hypothesis is needed for the route-price gauge.  Either some
component has nonzero holonomy, in which case it contains an actual odd-price
cycle, or the price integrates componentwise to one global vertex potential.
The canonical Baer specialization records the exact `00/11` residual price law
on the same full relay graph.
-/

open SimpleGraph

namespace Erdos85

/-- For arbitrary (possibly disconnected) routing and price graphs, either an
actual routing cycle has odd price, or one global F₂ vertex potential prices
every routing edge. -/
theorem exists_odd_graphEdgeIndicator_cycle_or_exists_globalVertexPotential
    {V : Type*} [DecidableEq V] (P K : SimpleGraph V) :
    (∃ (x : V) (c : P.Walk x x), c.IsCycle ∧
      f2WalkWeight (graphEdgeIndicator K) c = 1) ∨
    ∃ lam : V → ZMod 2, ∀ {u v}, P.Adj u v →
      graphEdgeIndicator K u v = lam u + lam v := by
  classical
  by_cases hodd : ∃ (u : V) (p : P.Walk u u),
      f2WalkWeight (graphEdgeIndicator K) p = 1
  · left
    obtain ⟨u, p, hp⟩ := hodd
    obtain ⟨x, c, hcycle, hcweight, _⟩ :=
      exists_odd_graphEdgeIndicator_cycle_of_closedWalk P K p hp
    exact ⟨x, c, hcycle, hcweight⟩
  · right
    apply exists_vertexPotential_of_f2WalkWeight_closed_eq_zero_global
      (graphEdgeIndicator K) (graphEdgeIndicator_symm K)
    intro u p
    have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact (hbinary _).resolve_right (fun hp => hodd ⟨u, p, hp⟩)

/-- Canonical Baer relay specialization of the global alternative.  The first
conjunct supplies the global odd-cycle/potential dichotomy on the full relay;
the second identifies its residual price exactly: ambient `00` transitions
have price zero, while nonambient `11` transitions are priced precisely when
their cubic adjacency entry vanishes. -/
theorem canonicalBaerRelay_odd_residual_cycle_or_globalVertexPotential_and_price
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q)
    (mate : V → V → V)
    (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
    (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
    (hfixed : ∀ p x, A.Adj p x → mate p x ≠ x)
    (hcanonical : ∀ p x, trianglePartnerEligible A p x →
      mate p x = trianglePartner A p x) :
    let P := witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed
    let K := binaryTransportResidualGraph A hq hreg
    ((∃ (x : V) (c : P.Walk x x), c.IsCycle ∧
        f2WalkWeight (graphEdgeIndicator K) c = 1) ∨
      ∃ lam : V → ZMod 2, ∀ {u v}, P.Adj u v →
        graphEdgeIndicator K u v = lam u + lam v) ∧
    ∀ {u v}, P.Adj u v →
      (K.Adj u v ↔ ¬ A.Adj u v ∧
        (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
          A.adjMatrix (ZMod 2)) u v = 0) := by
  dsimp only
  constructor
  · exact exists_odd_graphEdgeIndicator_cycle_or_exists_globalVertexPotential
      (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed)
      (binaryTransportResidualGraph A hq hreg)
  · intro u v hP
    exact canonicalBaerRelay_residual_adj_iff_not_adj_and_cube_eq_zero
      A hfree hq hreg mate hclosed hinvol hfixed hcanonical hP

end Erdos85

#print axioms Erdos85.exists_odd_graphEdgeIndicator_cycle_or_exists_globalVertexPotential
#print axioms Erdos85.canonicalBaerRelay_odd_residual_cycle_or_globalVertexPotential_and_price
