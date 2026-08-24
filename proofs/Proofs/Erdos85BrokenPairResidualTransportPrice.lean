import Proofs.Erdos85BinaryTransportResidualGraph
import Proofs.Erdos85BrokenPairTransportMatrixPrice

/-!
# Residual transport price of a broken pair

Broken-star endpoints are nonadjacent in the ambient graph, hence also in
`T`.  On such a pair the residual graph `K = H △ T` therefore equals `H`.
Combining this with the matrix price `H_xy = 1 + (A³)_xy` identifies the
exact graph-level K-price.
-/

open SimpleGraph

namespace Erdos85

/-- A broken pair is a `K`-edge exactly when its cubic adjacency price
vanishes over F₂. -/
theorem brokenPair_binaryTransportResidualGraph_adj_iff_cube_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, G.degree v = q) {p x y : V}
    (hxy : x ≠ y)
    (hpx : (triangleFreeEdgeGraph G).Adj p x)
    (hpy : (triangleFreeEdgeGraph G).Adj p y) :
    (binaryTransportResidualGraph G hq hreg).Adj x y ↔
      (G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2) *
        G.adjMatrix (ZMod 2)) x y = 0 := by
  have hnotG : ¬ G.Adj x y :=
    triangleFreeStar_endpoints_not_adj G hpx hpy
  have hnotT : ¬ (triangleFreeEdgeGraph G).Adj x y := by
    intro hT
    exact hnotG ((mem_triangleFreeNeighbors G x y).mp hT).1
  have hKiffH :
      (binaryTransportResidualGraph G hq hreg).Adj x y ↔
        (binaryTransportSupportGraph G hq hreg).Adj x y := by
    change (graphF2SymmetricDifference
      (binaryTransportSupportGraph G hq hreg)
      (triangleFreeEdgeGraph G)).Adj x y ↔ _
    rw [graphF2SymmetricDifference_adj_iff]
    constructor
    · rintro (⟨hH, _⟩ | ⟨_, hT⟩)
      · exact hH
      · exact (hnotT hT).elim
    · intro hH
      exact Or.inl ⟨hH, hnotT⟩
  rw [hKiffH]
  change binaryTransportMatrix G x y = 1 ↔ _
  have hprice := triangleFreeStar_transportMatrix_entry
    G hfree hxy hpx hpy
  rw [show binaryTransportMatrix G x y =
      1 + (G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2) *
        G.adjMatrix (ZMod 2)) x y by
    simpa [binaryTransportMatrix] using hprice]
  constructor <;> intro h
  · have := congrArg (fun z : ZMod 2 => z + 1) h
    simpa using this
  · rw [h, add_zero]

/-- Complementary form: a broken pair is absent from `K` exactly when its
cubic price is one. -/
theorem brokenPair_not_binaryTransportResidualGraph_adj_iff_cube_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, G.degree v = q) {p x y : V}
    (hxy : x ≠ y)
    (hpx : (triangleFreeEdgeGraph G).Adj p x)
    (hpy : (triangleFreeEdgeGraph G).Adj p y) :
    ¬ (binaryTransportResidualGraph G hq hreg).Adj x y ↔
      (G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2) *
        G.adjMatrix (ZMod 2)) x y = 1 := by
  rw [brokenPair_binaryTransportResidualGraph_adj_iff_cube_eq_zero
    G hfree hq hreg hxy hpx hpy]
  have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hbinary ((G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2) *
    G.adjMatrix (ZMod 2)) x y) with hzero | hone
  · simp [hzero]
  · simp [hone]

end Erdos85

#print axioms Erdos85.brokenPair_binaryTransportResidualGraph_adj_iff_cube_eq_zero
#print axioms Erdos85.brokenPair_not_binaryTransportResidualGraph_adj_iff_cube_eq_one
