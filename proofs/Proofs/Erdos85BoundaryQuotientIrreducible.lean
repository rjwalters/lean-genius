import Proofs.Erdos85BoundaryConnected
import Proofs.Erdos85SecondOrderQuotient

/-!
# Irreducibility of the second-order component quotient

At the second strict Moore boundary the original graph is connected.  Every
original edge gives a positive entry of the equitable quotient by defect
components, so the nonnegative integral quotient is irreducible.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- An edge of the original graph produces a positive entry in any equitable
component quotient. -/
theorem componentQuotientMatrix_pos_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (k : ℕ) (hreg : ∀ x : V, D.degree x = k)
    (hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ)
    {x y : V} (hxy : G.Adj x y) :
    0 < componentQuotientMatrix G D
      (D.connectedComponentMk x) (D.connectedComponentMk y) := by
  rw [componentQuotientMatrix_apply_eq G D k hreg hcomm
    (D.connectedComponentMk x) (D.connectedComponentMk y) (x := x) rfl]
  apply Finset.card_pos.mpr
  refine ⟨y, ?_⟩
  simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset, hxy]

/-- The support relation of the second-order component quotient connects
every ordered pair of defect components.  This is the standard
`ReflTransGen` formulation of irreducibility for a nonnegative matrix. -/
theorem secondOrder_componentQuotientMatrix_irreducible
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) :
    Relation.ReflTransGen
      (fun a b => 0 < componentQuotientMatrix G (secondOrderDefectGraph G) a b)
      c e := by
  classical
  let D := secondOrderDefectGraph G
  let x := componentRepresentative D c
  let y := componentRepresentative D e
  have hGcard : Fintype.card G.ConnectedComponent = 1 :=
    connected_of_second_strict_moore_order G hfree (by omega) hmin hcard
  have hcomponentEq : G.connectedComponentMk x = G.connectedComponentMk y := by
    exact (Fintype.card_le_one_iff.mp (by omega :
      Fintype.card G.ConnectedComponent ≤ 1)) _ _
  have hreach : G.Reachable x y :=
    SimpleGraph.ConnectedComponent.exact hcomponentEq
  have hwalk : Relation.ReflTransGen G.Adj x y :=
    (G.reachable_iff_reflTransGen x y).mp hreach
  have hlift : Relation.ReflTransGen
      (fun a b : D.ConnectedComponent =>
        0 < componentQuotientMatrix G D a b)
      (D.connectedComponentMk x) (D.connectedComponentMk y) :=
    hwalk.lift D.connectedComponentMk (fun u v huv =>
      componentQuotientMatrix_pos_of_adj G D 2
        (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard)
        (adjMatrix_comm_secondOrderDefect_of_even_real
          G hfree hd heven hmin hcard) huv)
  have hxc : D.connectedComponentMk x = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp
      (componentRepresentative_mem D c)
  have hye : D.connectedComponentMk y = e :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff e y).mp
      (componentRepresentative_mem D e)
  simpa [D, x, y, hxc, hye] using hlift

end

end Erdos85
