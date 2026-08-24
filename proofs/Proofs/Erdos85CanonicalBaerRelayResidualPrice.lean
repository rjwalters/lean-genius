import Proofs.Erdos85CanonicalBaerRelayBrokenPart
import Proofs.Erdos85ActiveBrokenRelayResidualPrice

/-!
# Residual price on the full canonical Baer relay

The global `00/11` decomposition identifies exactly which full paired-star
edges are broken relays.  Combining it with residual-price disjointness from
ambient edges and the broken-pair cubic formula gives one exact price law on
every edge of the full Eulerian relay.
-/

open SimpleGraph

namespace Erdos85

/-- **Full canonical relay price classification.** On a full paired-star
relay edge, residual K-adjacency is equivalent to being a non-ambient
(`11`) edge whose cubic adjacency entry vanishes.  In particular all
canonical ambient (`00`) edges have price zero. -/
theorem canonicalBaerRelay_residual_adj_iff_not_adj_and_cube_eq_zero
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
    {u v : V}
    (hP : (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed).Adj
      u v) :
    (binaryTransportResidualGraph A hq hreg).Adj u v ↔
      ¬ A.Adj u v ∧
      (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
        A.adjMatrix (ZMod 2)) u v = 0 := by
  let hbclosed := fun p x (hx : (triangleFreeEdgeGraph A).Adj p x) =>
    canonicalBaerMate_broken_closed A mate hclosed hinvol hcanonical hx
  let hbinvol := fun p x (hx : (triangleFreeEdgeGraph A).Adj p x) =>
    hinvol p x ((mem_triangleFreeNeighbors A p x).mp hx).1
  let hbfixed := fun p x (hx : (triangleFreeEdgeGraph A).Adj p x) =>
    hfixed p x ((mem_triangleFreeNeighbors A p x).mp hx).1
  have hdecomp :
      (canonicalBaerBrokenRelayGraph A mate hclosed hinvol hfixed
        hcanonical).Adj u v ↔ _ :=
    canonicalBaerBrokenRelayGraph_adj_iff_fullRelay_and_not_adj
      A mate hclosed hinvol hfixed hcanonical
  constructor
  · intro hK
    have hnotA : ¬ A.Adj u v := by
      intro hA
      have hboth : (binaryTransportResidualGraph A hq hreg ⊓ A).Adj u v :=
        ⟨hK, hA⟩
      rw [binaryTransportResidualGraph_inf_eq_bot A hfree hq hreg] at hboth
      exact hboth
    have hR : (canonicalBaerBrokenRelayGraph A mate hclosed hinvol hfixed
      hcanonical).Adj u v := hdecomp.mpr ⟨hP, hnotA⟩
    refine ⟨hnotA, ?_⟩
    exact (activeBrokenRelay_adj_residual_iff_cube_eq_zero
      A hfree hq hreg (fun _ => True) mate hbclosed hbinvol hbfixed
      hR).mp hK
  · rintro ⟨hnotA, hcubic⟩
    have hR : (canonicalBaerBrokenRelayGraph A mate hclosed hinvol hfixed
      hcanonical).Adj u v := hdecomp.mpr ⟨hP, hnotA⟩
    exact (activeBrokenRelay_adj_residual_iff_cube_eq_zero
      A hfree hq hreg (fun _ => True) mate hbclosed hbinvol hbfixed
      hR).mpr hcubic

end Erdos85

#print axioms Erdos85.canonicalBaerRelay_residual_adj_iff_not_adj_and_cube_eq_zero
