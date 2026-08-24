import Proofs.Erdos85GlobalOddCycleOrPotential

/-!
# Endpoint potentials on the canonical Baer relay

This is the endpoint form of `(73rnz_cjibkr)`: in the additive branch,
canonical ambient `00` transitions preserve the potential, while a broken
`11` transition flips it exactly when its cubic residual price is nonzero.
-/

open SimpleGraph

namespace Erdos85

/-- On a binary graph-priced routing edge, adjacency in the price graph is
equivalent to unequal endpoint potentials. -/
theorem graphEdgeIndicator_adj_iff_endpointPotential_ne
    {V : Type*} {P K : SimpleGraph V} {lam : V → ZMod 2}
    (hpotential : ∀ {u v}, P.Adj u v →
      graphEdgeIndicator K u v = lam u + lam v)
    {u v : V} (huv : P.Adj u v) :
    K.Adj u v ↔ lam u ≠ lam v := by
  constructor
  · exact endpointPotential_ne_of_priceEdge hpotential huv
  · intro hne
    by_contra hnotK
    exact hne (endpointPotential_eq_of_not_priceEdge
      hpotential huv hnotK)

/-- An ambient (`00`) edge of the full canonical relay has equal endpoint
potentials in the global additive branch. -/
theorem canonicalBaerRelay_endpointPotential_eq_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q)
    (mate : V → V → V)
    (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
    (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
    (hfixed : ∀ p x, A.Adj p x → mate p x ≠ x)
    (hcanonical : ∀ p x, trianglePartnerEligible A p x →
      mate p x = trianglePartner A p x)
    (lam : V → ZMod 2)
    (hpotential : ∀ {u v},
      (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed).Adj u v →
      graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) u v =
        lam u + lam v)
    {u v : V}
    (hP : (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed).Adj
      u v) (hA : A.Adj u v) :
    lam u = lam v := by
  apply endpointPotential_eq_of_not_priceEdge hpotential hP
  intro hK
  have hclass :=
    (canonicalBaerRelay_residual_adj_iff_not_adj_and_cube_eq_zero
      A hfree hq hreg mate hclosed hinvol hfixed hcanonical hP).mp hK
  exact hclass.1 hA

/-- On a nonambient (`11`) full-relay edge, endpoint potentials differ exactly
when the cubic adjacency entry vanishes, i.e. exactly when the residual price
graph contains the edge. -/
theorem canonicalBaerRelay_endpointPotential_ne_iff_cube_eq_zero_of_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q)
    (mate : V → V → V)
    (hclosed : ∀ p x, A.Adj p x → A.Adj p (mate p x))
    (hinvol : ∀ p x, A.Adj p x → mate p (mate p x) = x)
    (hfixed : ∀ p x, A.Adj p x → mate p x ≠ x)
    (hcanonical : ∀ p x, trianglePartnerEligible A p x →
      mate p x = trianglePartner A p x)
    (lam : V → ZMod 2)
    (hpotential : ∀ {u v},
      (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed).Adj u v →
      graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) u v =
        lam u + lam v)
    {u v : V}
    (hP : (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed).Adj
      u v) (hnotA : ¬ A.Adj u v) :
    lam u ≠ lam v ↔
      (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
        A.adjMatrix (ZMod 2)) u v = 0 := by
  have hclass := canonicalBaerRelay_residual_adj_iff_not_adj_and_cube_eq_zero
    A hfree hq hreg mate hclosed hinvol hfixed hcanonical hP
  have hprice := graphEdgeIndicator_adj_iff_endpointPotential_ne
    hpotential hP
  constructor
  · intro hne
    exact (hclass.mp (hprice.mpr hne)).2
  · intro hcubic
    exact hprice.mp (hclass.mpr ⟨hnotA, hcubic⟩)

end Erdos85

#print axioms Erdos85.graphEdgeIndicator_adj_iff_endpointPotential_ne
#print axioms Erdos85.canonicalBaerRelay_endpointPotential_eq_of_adj
#print axioms Erdos85.canonicalBaerRelay_endpointPotential_ne_iff_cube_eq_zero_of_not_adj
