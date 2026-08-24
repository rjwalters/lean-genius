import Proofs.Erdos85BinaryTransportSupportGraph
import Proofs.Erdos85C4FreeRegularAdjacencyCube

/-!
# The transport graph on ambient edges

For a C4-free regular graph, the binary transport graph
`H = supp(A²(A+I))` agrees on ambient edges with the spanning subgraph `T`
of edges lying in no triangle.  Equivalently, `H ∩ A = T`; this is audit
identity (18), which makes `K = H △ T` disjoint from `A`.
-/

open SimpleGraph

namespace Erdos85

/-- On an ambient edge, the cubic adjacency entry is one modulo two. -/
theorem adjMatrix_cube_zmodTwo_apply_of_adj_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (q : ℕ)
    (hreg : ∀ v, G.degree v = q) {x y : V} (hxy : G.Adj x y) :
    (G.adjMatrix (ZMod 2) * G.adjMatrix (ZMod 2) *
      G.adjMatrix (ZMod 2)) x y = 1 := by
  let Aℤ := G.adjMatrix ℤ
  let A₂ := G.adjMatrix (ZMod 2)
  have hcube := c4Free_regular_adjMatrix_cube_apply_of_adj
    G hfree q hreg hxy
  have hmap : ((Aℤ * Aℤ * Aℤ).map (Int.castRingHom (ZMod 2))) =
      A₂ * A₂ * A₂ := by
    have hadj : Aℤ.map (Int.castRingHom (ZMod 2)) = A₂ := by
      ext u v
      simp [Aℤ, A₂, Matrix.map_apply, SimpleGraph.adjMatrix_apply]
    rw [Matrix.map_mul, Matrix.map_mul, hadj]
  rw [← congr_fun₂ hmap x y, Matrix.map_apply, hcube]
  rw [map_sub, map_mul]
  change ((2 : ℤ) : ZMod 2) * ((q : ℤ) : ZMod 2) -
    ((1 : ℤ) : ZMod 2) = 1
  have htwo : ((2 : ℤ) : ZMod 2) = 0 := by decide
  rw [htwo, zero_mul, zero_sub]
  decide

/-- **Transport/triangle interface.**  On every edge of `G`, adjacency in
the transport support graph is equivalent to lying in no triangle. -/
theorem binaryTransportSupportGraph_adj_iff_triangleFreeEdgeGraph_adj_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, G.degree v = q) {x y : V} (hxy : G.Adj x y) :
    (binaryTransportSupportGraph G hq hreg).Adj x y ↔
      (triangleFreeEdgeGraph G).Adj x y := by
  have hne : x ≠ y := by
    intro h
    subst y
    exact G.loopless.irrefl x hxy
  have hcommonLe :
      (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1 :=
    common_le_one_of_not_containsC4 hfree x y hne
  have hcube := adjMatrix_cube_zmodTwo_apply_of_adj_eq_one
    G hfree q hreg hxy
  change binaryTransportMatrix G x y = 1 ↔ _
  rw [binaryTransportMatrix_eq_cube_add_sq, Matrix.add_apply]
  have hcubePow : (G.adjMatrix (ZMod 2) ^ 3) x y = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using hcube
  rw [hcubePow]
  constructor
  · intro htransport
    have hsquareZero : (G.adjMatrix (ZMod 2) ^ 2) x y = 0 := by
      have := congrArg (fun z : ZMod 2 => z + 1) htransport
      simpa using this
    rw [pow_two, adjMatrix_sq_apply_eq_card_common_zmodTwo] at hsquareZero
    have hcardZero : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 := by
      interval_cases hcard : (G.neighborFinset x ∩ G.neighborFinset y).card
      · rfl
      · norm_num at hsquareZero
    exact (mem_triangleFreeNeighbors G x y).mpr ⟨hxy, hcardZero⟩
  · intro htriangleFree
    have hcardZero := ((mem_triangleFreeNeighbors G x y).mp htriangleFree).2
    rw [pow_two, adjMatrix_sq_apply_eq_card_common_zmodTwo, hcardZero]
    norm_num

/-- Graph-level form of audit identity (18): `H ∩ A = T`. -/
theorem binaryTransportSupportGraph_inf_eq_triangleFreeEdgeGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : Even q)
    (hreg : ∀ v, G.degree v = q) :
    binaryTransportSupportGraph G hq hreg ⊓ G = triangleFreeEdgeGraph G := by
  ext x y
  simp only [SimpleGraph.inf_adj]
  constructor
  · rintro ⟨hH, hG⟩
    exact (binaryTransportSupportGraph_adj_iff_triangleFreeEdgeGraph_adj_of_adj
      G hfree hq hreg hG).mp hH
  · intro hT
    have hG := ((mem_triangleFreeNeighbors G x y).mp hT).1
    exact ⟨(binaryTransportSupportGraph_adj_iff_triangleFreeEdgeGraph_adj_of_adj
      G hfree hq hreg hG).mpr hT, hG⟩

end Erdos85

#print axioms Erdos85.adjMatrix_cube_zmodTwo_apply_of_adj_eq_one
#print axioms Erdos85.binaryTransportSupportGraph_adj_iff_triangleFreeEdgeGraph_adj_of_adj
#print axioms Erdos85.binaryTransportSupportGraph_inf_eq_triangleFreeEdgeGraph
