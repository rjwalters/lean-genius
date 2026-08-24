import Proofs.Erdos85BinarySquareDyadicSignedTerminal
import Proofs.Erdos85BinarySquareNoSizeQDefectClique

/-!
# No order-q replication-one exceptional support at even degree

This is the graph-native interface between the Baer replication census and
the even-degree defect-component obstruction.  Replication at most one makes
the support a clique in the second-order defect graph; an order-`q` such
clique is impossible at binary-square order.
-/

open SimpleGraph

namespace Erdos85

/-- At even binary-square degree, a support of cardinality `q` cannot have
ambient point-replication at most one. -/
theorem binarySquare_regular_no_sizeQ_support_of_replicationAtMostOne_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (C : Finset V) (hCcard : C.card = q)
    (hcap : ∀ v, (G.neighborFinset v ∩ C).card ≤ 1) : False := by
  apply binarySquare_regular_no_sizeQ_secondOrderDefect_clique_of_even
    G hfree hq hqEven hreg hcard C hCcard
  intro u v hu hv huv
  exact replicationAtMostOne_secondOrderDefect_adj
    G hfree C hcap hu hv huv

end Erdos85

#print axioms Erdos85.binarySquare_regular_no_sizeQ_support_of_replicationAtMostOne_of_even
