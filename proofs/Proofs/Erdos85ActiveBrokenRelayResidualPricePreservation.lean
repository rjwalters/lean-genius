import Proofs.Erdos85BrokenPairResidualTransportPrice
import Proofs.Erdos85ActiveBrokenRelayEulerizationEvenRegular

/-!
# Residual-price preservation under relay Eulerization

The exact Eulerization `Q_s = R_s △ δ_T(supp s)` adds only ambient
`T`-edges.  Since the residual transport graph `K` is disjoint from the
ambient graph, those boundary payments have zero K-price.  Thus
`Q_s ∩ K = R_s ∩ K`, the graph-level content of audit (73rnz_cjibi).
-/

open SimpleGraph

namespace Erdos85

/-- Symmetric difference with a graph disjoint from `K` preserves the
intersection with `K`. -/
theorem graphF2SymmetricDifference_inf_eq_left_inf_of_right_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (R C K : SimpleGraph V)
    [DecidableRel R.Adj] [DecidableRel C.Adj] [DecidableRel K.Adj]
    (hdisjoint : ∀ x y, C.Adj x y → K.Adj x y → False) :
    graphF2SymmetricDifference R C ⊓ K = R ⊓ K := by
  ext x y
  simp only [SimpleGraph.inf_adj]
  constructor
  · rintro ⟨hxor, hK⟩
    rcases (graphF2SymmetricDifference_adj_iff R C x y).mp hxor with
      ⟨hR, _⟩ | ⟨_, hC⟩
    · exact ⟨hR, hK⟩
    · exact (hdisjoint x y hC hK).elim
  · rintro ⟨hR, hK⟩
    have hnC : ¬ C.Adj x y := fun hC => hdisjoint x y hC hK
    exact ⟨(graphF2SymmetricDifference_adj_iff R C x y).mpr
      (Or.inl ⟨hR, hnC⟩), hK⟩

/-- Every cut edge of `T` has zero residual K-price. -/
theorem triangleFreeCut_disjoint_binaryTransportResidualGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, G.degree v = q) (S : Finset V) {x y : V}
    (hcut : (binaryVertexCutGraph (triangleFreeEdgeGraph G) S).Adj x y)
    (hK : (binaryTransportResidualGraph G hq hreg).Adj x y) : False := by
  have hT : (triangleFreeEdgeGraph G).Adj x y := hcut.1
  have hG : G.Adj x y := ((mem_triangleFreeNeighbors G x y).mp hT).1
  have hboth :
      (binaryTransportResidualGraph G hq hreg ⊓ G).Adj x y := ⟨hK, hG⟩
  rw [binaryTransportResidualGraph_inf_eq_bot G hfree hq hreg] at hboth
  exact hboth

/-- **Exact price preservation in (73rnz_cjibi).**  Eulerizing the active
broken relay by the triangle-free cut does not change its K-edge subgraph. -/
theorem activeBrokenRelay_cut_symmDiff_inf_residual_eq
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
      mate w v ≠ v) :
    graphF2SymmetricDifference
        (activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
          hclosed hinvol hfixed)
        (binaryVertexCutGraph (triangleFreeEdgeGraph A)
          (f2PotentialSupport x)) ⊓
        binaryTransportResidualGraph A hq hreg =
      activeBrokenWitnessRelayGraph A (fun w => x w = 1) mate
          hclosed hinvol hfixed ⊓
        binaryTransportResidualGraph A hq hreg := by
  apply graphF2SymmetricDifference_inf_eq_left_inf_of_right_disjoint
  intro u v hcut hK
  exact triangleFreeCut_disjoint_binaryTransportResidualGraph
    A hfree hq hreg (f2PotentialSupport x) hcut hK

end Erdos85

#print axioms Erdos85.graphF2SymmetricDifference_inf_eq_left_inf_of_right_disjoint
#print axioms Erdos85.triangleFreeCut_disjoint_binaryTransportResidualGraph
#print axioms Erdos85.activeBrokenRelay_cut_symmDiff_inf_residual_eq
