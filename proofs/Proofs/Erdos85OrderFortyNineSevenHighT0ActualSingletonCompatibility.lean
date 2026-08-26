import Proofs.Erdos85OrderFortyNineSevenHighT0EmptyQuotient
import Proofs.Erdos85GadgetExtension

/-!
# Actual-singleton compatibility in the seven-high empty-triple case

The quotient search must distinguish the two actual singleton-support vertices
carrying a fixed high label.  The sound `C₄` constraint is therefore phrased
directly in terms of graph vertices: two distinct roots have at most one common
singleton-support neighbor.  If a non-singleton common neighbor is already
known, they have no common singleton-support neighbor.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The actual singleton-support common neighbors of two distinct vertices
have cardinality at most one.  This deliberately does not identify the two
singleton vertices carrying the same high label. -/
theorem sevenHigh_t0_actualSingleton_commonNeighbor_card_le_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    {x y : Fin 49} (hxy : x ≠ y) :
    ((G.neighborFinset x ∩ G.neighborFinset y).filter fun z =>
      (orderFortyNineHighSupport G z).card = 1).card ≤ 1 := by
  exact (Finset.card_filter_le _ _).trans
    ((not_containsC4_iff_forall_common_le_one G).mp hfree x y hxy)

/-- Once two distinct vertices already share a non-singleton vertex, they
cannot share any actual singleton-support vertex: that would give two common
neighbors and hence a `C₄`. -/
theorem sevenHigh_t0_actualSingleton_commonNeighbor_eq_empty_of_common_nonSingleton
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    {x y z : Fin 49} (hxy : x ≠ y)
    (hzx : G.Adj z x) (hzy : G.Adj z y)
    (hzNotSingleton : (orderFortyNineHighSupport G z).card ≠ 1) :
    (G.neighborFinset x ∩ G.neighborFinset y).filter (fun w =>
      (orderFortyNineHighSupport G w).card = 1) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hwCommon := (Finset.mem_filter.mp hw).1
  have hwSingleton := (Finset.mem_filter.mp hw).2
  have hzCommon : z ∈ G.neighborFinset x ∩ G.neighborFinset y := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hzx.symm, hzy.symm⟩
  have hcard := (not_containsC4_iff_forall_common_le_one G).mp hfree x y hxy
  have hwz : w = z := Finset.card_le_one.mp hcard w hwCommon z hzCommon
  exact hzNotSingleton (hwz ▸ hwSingleton)

end

end Erdos85

#print axioms Erdos85.sevenHigh_t0_actualSingleton_commonNeighbor_card_le_one
#print axioms Erdos85.sevenHigh_t0_actualSingleton_commonNeighbor_eq_empty_of_common_nonSingleton
