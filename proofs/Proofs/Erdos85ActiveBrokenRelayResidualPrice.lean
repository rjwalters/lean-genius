import Proofs.Erdos85EulerianOddResidualHolonomy

/-!
# Unique witness and residual price of active broken-relay edges

Every edge of the active broken relay has a unique active witness.  The
residual K-price of that edge is therefore canonically its cubic adjacency
predicate, with no choice of witness left in the downstream owner ledger.
-/

open SimpleGraph

namespace Erdos85

/-- An active broken-relay edge has a unique active witness label. -/
theorem activeBrokenWitnessRelayGraph_existsUnique_witness
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) (active : V → Prop) [DecidablePred active]
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v) {x y : V}
    (hxy : (activeBrokenWitnessRelayGraph A active mate
      hclosed hinvol hfixed).Adj x y) :
    ∃! w, active w ∧ (triangleFreeEdgeGraph A).Adj w x ∧ mate w x = y := by
  change ∃ w, (active w ∧ (triangleFreeEdgeGraph A).Adj w x) ∧
    mate w x = y at hxy
  obtain ⟨w, ⟨hwactive, hwx⟩, hwmate⟩ := hxy
  refine ⟨w, ⟨hwactive, hwx, hwmate⟩, ?_⟩
  intro w' hw'
  have hne : x ≠ y := by
    rw [← hwmate]
    exact (hfixed w x hwx).symm
  have hsub : ∀ {u v}, (triangleFreeEdgeGraph A).Adj u v → A.Adj u v := by
    intro u v huv
    exact ((mem_triangleFreeNeighbors A u v).mp huv).1
  have hwy : A.Adj y w := by
    rw [← hwmate]
    exact (hsub (hclosed w x hwx)).symm
  have hw'y : A.Adj y w' := by
    rw [← hw'.2.2]
    exact (hsub (hclosed w' x hw'.2.1)).symm
  exact commonNeighbor_unique_of_c4Free hfree hne
    (hsub hw'.2.1).symm hw'y (hsub hwx).symm hwy

/-- Every active broken-relay edge has the exact graph-level residual price:
it lies in `K` iff its cubic adjacency entry is zero over F₂. -/
theorem activeBrokenRelay_adj_residual_iff_cube_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q) (active : V → Prop)
    [DecidablePred active] (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v) {x y : V}
    (hR : (activeBrokenWitnessRelayGraph A active mate
      hclosed hinvol hfixed).Adj x y) :
    (binaryTransportResidualGraph A hq hreg).Adj x y ↔
      (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
        A.adjMatrix (ZMod 2)) x y = 0 := by
  obtain ⟨w, hw, _⟩ := activeBrokenWitnessRelayGraph_existsUnique_witness
    A hfree active mate hclosed hinvol hfixed hR
  have hne : x ≠ y := by
    intro h
    subst y
    exact (activeBrokenWitnessRelayGraph A active mate
      hclosed hinvol hfixed).loopless.irrefl x hR
  exact brokenPair_binaryTransportResidualGraph_adj_iff_cube_eq_zero
    A hfree hq hreg hne hw.2.1 (by simpa [hw.2.2] using hclosed w x hw.2.1)

end Erdos85

#print axioms Erdos85.activeBrokenWitnessRelayGraph_existsUnique_witness
#print axioms Erdos85.activeBrokenRelay_adj_residual_iff_cube_eq_zero
