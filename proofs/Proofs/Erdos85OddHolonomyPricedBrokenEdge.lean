import Proofs.Erdos85ActiveBrokenRelayResidualPrice
import Proofs.Erdos85DisconnectedEulerianOddResidualHolonomy

/-!
# Extracting a priced broken pair from odd holonomy

An odd graph-indicator walk contains an actual priced dart.  For the active
broken Eulerization, residual-price preservation identifies that dart with
an active broken relay edge; unique witnessing and the cubic price law then
produce a concrete broken pair with zero cubic entry.
-/

open SimpleGraph

namespace Erdos85

/-- A walk of odd K-indicator weight contains an actual edge of both the
routing graph and the price graph. -/
theorem exists_priceEdge_of_f2WalkWeight_graphEdgeIndicator_eq_one
    {V : Type*} {P K : SimpleGraph V} {u v : V}
    (p : P.Walk u v)
    (hw : f2WalkWeight (graphEdgeIndicator K) p = 1) :
    ∃ x y, P.Adj x y ∧ K.Adj x y ∧ s(x, y) ∈ p.edges := by
  induction p with
  | nil => simp at hw
  | @cons a b c hab p ih =>
      by_cases hK : K.Adj a b
      · exact ⟨a, b, hab, hK, by simp⟩
      · have hi : graphEdgeIndicator K a b = 0 := by
          simp [graphEdgeIndicator, hK]
        rw [f2WalkWeight_cons, hi, zero_add] at hw
        obtain ⟨x, y, hP, hKxy, hedge⟩ := ih hw
        exact ⟨x, y, hP, hKxy, by simp [hedge]⟩

/-- An odd residual-price walk in `Q_s` exposes a concrete active broken
pair, with its unique active witness and zero cubic adjacency entry. -/
theorem activeBrokenRelay_exists_priced_brokenPair_of_odd_walk
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, A.degree v = q) (x : V → ZMod 2)
    (mate : V → V → V)
    (hclosed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      (triangleFreeEdgeGraph A).Adj w (mate w v))
    (hinvol : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w (mate w v) = v)
    (hfixed : ∀ w v, (triangleFreeEdgeGraph A).Adj w v →
      mate w v ≠ v)
    {root : V}
    (p : (graphF2SymmetricDifference
      (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
        hclosed hinvol hfixed)
      (binaryVertexCutGraph (triangleFreeEdgeGraph A)
        (f2PotentialSupport x))).Walk root root)
    (hp : f2WalkWeight (graphEdgeIndicator
      (binaryTransportResidualGraph A hq hreg)) p = 1) :
    ∃ a b w,
      x w = 1 ∧
      (triangleFreeEdgeGraph A).Adj w a ∧
      mate w a = b ∧
      (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
        A.adjMatrix (ZMod 2)) a b = 0 ∧
      s(a, b) ∈ p.edges := by
  obtain ⟨a, b, hQ, hK, hedge⟩ :=
    exists_priceEdge_of_f2WalkWeight_graphEdgeIndicator_eq_one p hp
  have hQK : (graphF2SymmetricDifference
      (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
        hclosed hinvol hfixed)
      (binaryVertexCutGraph (triangleFreeEdgeGraph A)
        (f2PotentialSupport x)) ⊓
      binaryTransportResidualGraph A hq hreg).Adj a b := ⟨hQ, hK⟩
  rw [activeBrokenRelay_cut_symmDiff_inf_residual_eq
    A hfree hq hreg x mate hclosed hinvol hfixed] at hQK
  obtain ⟨w, hw, _⟩ := activeBrokenWitnessRelayGraph_existsUnique_witness
    A hfree (fun w => x w = 1) mate hclosed hinvol hfixed hQK.1
  refine ⟨a, b, w, hw.1, hw.2.1, hw.2.2, ?_, hedge⟩
  exact (activeBrokenRelay_adj_residual_iff_cube_eq_zero
    A hfree hq hreg (fun w => x w = 1) mate hclosed hinvol hfixed
    hQK.1).mp hQK.2

end Erdos85

#print axioms Erdos85.exists_priceEdge_of_f2WalkWeight_graphEdgeIndicator_eq_one
#print axioms Erdos85.activeBrokenRelay_exists_priced_brokenPair_of_odd_walk
