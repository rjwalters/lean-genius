import Proofs.Erdos85BoundaryConnectedClean
import Proofs.Erdos85BoundaryQuotientIrreducible

/-! A clean-axiom version of boundary quotient irreducibility. -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The support relation of the second-order component quotient connects
every ordered pair, without using the classified strict Moore bound. -/
theorem secondOrder_componentQuotientMatrix_irreducible_clean
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
      (fun a b => 0 < componentQuotientMatrix G
        (secondOrderDefectGraph G) a b) c e := by
  classical
  let D := secondOrderDefectGraph G
  let x := componentRepresentative D c
  let y := componentRepresentative D e
  have hGcard : Fintype.card G.ConnectedComponent = 1 :=
    connected_of_secondOrder_boundary_clean G hfree (by omega) hmin hcard
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
