import Proofs.Erdos85DistanceLayers

/-! # Adjacent root branches are cross-independent -/

namespace Erdos85

open SimpleGraph

/-- In a `C₄`-free graph, second-layer vertices belonging to adjacent
first-neighbor branches cannot be adjacent: such an edge would close the rim
`p-s-t-q-p`. -/
theorem not_adj_between_adjacent_secondLayerBranches
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1)
    {p q : V}
    (hp : p ∈ secondLayerBranch G v s)
    (hq : q ∈ secondLayerBranch G v t) :
    ¬ G.Adj p q := by
  intro hpq
  have hsp : G.Adj s.1 p :=
    (G.mem_neighborFinset s.1 p).mp (Finset.mem_sdiff.mp hp).1
  have htq : G.Adj t.1 q :=
    (G.mem_neighborFinset t.1 q).mp (Finset.mem_sdiff.mp hq).1
  have hstne : s ≠ t := fun h =>
    (G.ne_of_adj hst) (congrArg Subtype.val h)
  have hdisj : Disjoint (secondLayerBranch G v s)
      (secondLayerBranch G v t) :=
    secondLayerBranch_pairwiseDisjoint G hfree v
      (by simp) (by simp) hstne
  have hpqne : p ≠ q := fun h => by
    subst q
    exact Finset.disjoint_left.mp hdisj hp hq
  have hpt : p ≠ t.1 := by
    intro h
    subst p
    exact (Finset.mem_sdiff.mp hp).2 (by
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr t.2)
  have hsq : s.1 ≠ q := by
    intro h
    subst q
    exact (Finset.mem_sdiff.mp hq).2 (by
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr s.2)
  exact hfree (containsC4_of_rim
    hsp.symm hst htq hpq.symm
    hpt hsq (G.ne_of_adj hsp) (G.ne_of_adj hst)
    hpqne.symm (G.ne_of_adj htq).symm)

end Erdos85
