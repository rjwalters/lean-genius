import Proofs.Erdos85OneHighMateMissHexagonGraph
import Proofs.Erdos85OneHighOddLabelCycleSources
import Proofs.Erdos85OneHighRootPairGraphDecoder

/-! # Consuming the mate-edge sector of an odd label cycle -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A cycle dart whose two root labels have the same canonical mate-pair
color carries an odd multiplicity on an adjacent root pair, and therefore
produces the concrete mate-miss hexagon configuration. -/
theorem exists_oneHighMateMissHexagon_of_oddLabelCycle_mateEdge
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s, branchLabel (rootMate s) =
      oneHighStandardMate (branchLabel s))
    {l : {z : V // z ∈ G.neighborSet v}}
    {c : (oddExchangedKeyLabelGraph
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj))).Walk l l}
    (hc : c.IsCycle) (i : Fin c.length)
    (hpair : oneHighRootPair (branchLabel (c.getVert i.1)) =
      oneHighRootPair (branchLabel
        (c.getVert (oneHighCycleNext c hc i).1))) :
    Nonempty (OneHighMateMissHexagon G v) := by
  let u := c.getVert i.1
  let w := c.getVert (oneHighCycleNext c hc i).1
  have hadj : (oddExchangedKeyLabelGraph
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj))).Adj u w := by
    dsimp [u, w]
    rw [getVert_oneHighCycleNext c hc i]
    exact c.adj_getVert_succ i.2
  have humate : u = rootMate w := by
    rcases (oneHighRootPair_branchLabel_eq_iff_eq_or_rootMate
      rootMate branchLabel hbranchMate u w).mp hpair with heq | hmate
    · exact (hadj.1 heq).elim
    · exact hmate
  have huw : G.Adj u.1 w.1 := by
    rw [humate]
    exact (hrootAdj w).symm
  exact exists_oneHighMateMissHexagon_of_oddMultiplicity
    G hfree hv hexternal houterDegree rootMate hrootAdj u w huw hadj.2

end

end Erdos85
