import Proofs.Erdos85ActiveBrokenRelayResidualPriceFiber
import Proofs.Erdos85ActiveBrokenRelayOddResidualCycle

/-!
# Odd local price sum produces an odd residual relay cycle

This is the assembled scalar terminal of `(73rnz_cjibi)`: the local witness
prices `Theta_w` sum to the residual price of `R_s`; Eulerization preserves
that price; and odd Eulerian price produces an actual odd-K cycle in `Q_s`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If the sum of active-witness residual price fibers is odd, the active
broken Eulerization contains an actual cycle of odd residual K-weight. -/
theorem activeBrokenRelay_exists_odd_residual_cycle_of_odd_priceFiberSum
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
    (hodd : Odd (∑ w : V,
      activeBrokenRelayResidualPriceFiberCard A hfree hq hreg
        (fun w => x w = 1) mate hclosed hinvol hfixed w)) :
    ∃ (u : V) (c : (graphF2SymmetricDifference
        (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
          hclosed hinvol hfixed)
        (binaryVertexCutGraph (triangleFreeEdgeGraph A)
          (f2PotentialSupport x))).Walk u u),
      c.IsCycle ∧
      f2WalkWeight (graphEdgeIndicator
        (binaryTransportResidualGraph A hq hreg)) c = 1 := by
  let Q := graphF2SymmetricDifference
    (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
      hclosed hinvol hfixed)
    (binaryVertexCutGraph (triangleFreeEdgeGraph A) (f2PotentialSupport x))
  let R := activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
    hclosed hinvol hfixed
  let K := binaryTransportResidualGraph A hq hreg
  have hgraph : Q ⊓ K = R ⊓ K := by
    exact activeBrokenRelay_cut_symmDiff_inf_residual_eq
      A hfree hq hreg x mate hclosed hinvol hfixed
  have hcard : (Q ⊓ K).edgeFinset.card = (R ⊓ K).edgeFinset.card := by
    have hedge : (Q ⊓ K).edgeFinset = (R ⊓ K).edgeFinset := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset]
      have hm := congrArg (fun H : SimpleGraph V => e ∈ H.edgeSet) hgraph
      constructor
      · exact Eq.mp hm
      · exact Eq.mpr hm
    exact congrArg Finset.card hedge
  have hsum : (R ⊓ K).edgeFinset.card = ∑ w : V,
      activeBrokenRelayResidualPriceFiberCard A hfree hq hreg
        (fun w => x w = 1) mate hclosed hinvol hfixed w := by
    exact activeBrokenRelay_inf_residual_card_eq_sum_priceFiberCard
      A hfree hq hreg (fun w => x w = 1) mate hclosed hinvol hfixed
  have hoddQ : Odd ((Q ⊓ K).edgeFinset.card) := by
    rw [hcard, hsum]
    exact hodd
  exact activeBrokenRelay_exists_odd_residual_cycle
    A hfree hq hreg x mate hclosed hinvol hfixed hoddQ

end

end Erdos85

#print axioms Erdos85.activeBrokenRelay_exists_odd_residual_cycle_of_odd_priceFiberSum
