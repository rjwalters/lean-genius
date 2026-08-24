import Proofs.Erdos85BinarySquareNoSizeQDefectClique
import Proofs.Erdos85BinarySquareDyadicSignedTerminal

/-!
# No full-empty exceptional core of size q

This is the graph-native interface for the exceptional Baer core.  Within
each exceptional type, point replication at most one forces a defect clique;
between a full and an empty line, their incompatible shore occupancies force
a defect edge.  Thus a size-`q` union would be a forbidden size-`q` defect
clique at even degree.
-/

open SimpleGraph

namespace Erdos85

/-- Full and empty line families of point-replication at most one cannot
together contain exactly `q` centers in the even binary-square setting. -/
theorem binarySquare_regular_no_fullEmpty_sizeQ_core_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S full empty : Finset V)
    (hfull : ∀ x ∈ full, (G.neighborFinset x ∩ S).card = q)
    (hempty : ∀ x ∈ empty, (G.neighborFinset x ∩ S).card = 0)
    (hfullCap : ∀ v, (G.neighborFinset v ∩ full).card ≤ 1)
    (hemptyCap : ∀ v, (G.neighborFinset v ∩ empty).card ≤ 1)
    (hcoreCard : (full ∪ empty).card = q) : False := by
  have hcoreClique : ∀ ⦃u v⦄, u ∈ full ∪ empty → v ∈ full ∪ empty →
      u ≠ v → (secondOrderDefectGraph G).Adj u v := by
    intro u v hu hv huv
    rcases Finset.mem_union.mp hu with huFull | huEmpty
    · rcases Finset.mem_union.mp hv with hvFull | hvEmpty
      · exact replicationAtMostOne_secondOrderDefect_adj
          G hfree full hfullCap huFull hvFull huv
      · exact binarySquare_full_empty_secondOrderDefect_adj
          G hfree (by omega) hreg S (hfull u huFull) (hempty v hvEmpty)
    · rcases Finset.mem_union.mp hv with hvFull | hvEmpty
      · exact (binarySquare_full_empty_secondOrderDefect_adj
          G hfree (by omega) hreg S (hfull v hvFull) (hempty u huEmpty)).symm
      · exact replicationAtMostOne_secondOrderDefect_adj
          G hfree empty hemptyCap huEmpty hvEmpty huv
  exact binarySquare_regular_no_sizeQ_secondOrderDefect_clique_of_even
    G hfree hq hqEven hreg hcard (full ∪ empty) hcoreCard hcoreClique

end Erdos85

#print axioms Erdos85.binarySquare_regular_no_fullEmpty_sizeQ_core_of_even
