import Proofs.Erdos85OneHighOddLabelCycleSources
import Proofs.Erdos85OneHighSourcePairTurnRefinement

/-! # Exact source branches at a cyclic odd-label turn -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- At any three-distinct-pair turn of a source-colored genuine cycle, the
two consecutive source branches are equal, are root mates, or one source
pair is the pair of the opposite outer endpoint.  This includes turns that
cross the chosen walk endpoint. -/
theorem oneHigh_sourceColoring_cyclic_turn_fourWay
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s, branchLabel (rootMate s) =
      oneHighStandardMate (branchLabel s))
    {H : SimpleGraph {z : V // z ∈ G.neighborSet v}}
    {l : {z : V // z ∈ G.neighborSet v}} {c : H.Walk l l}
    (hc : c.IsCycle)
    (source : Fin c.length → OneHighAllMatchedVertices G v)
    (hfar : ∀ i : Fin c.length,
      c.getVert i.1 ∈
        ((Finset.univ.erase (source i).1).erase (rootMate (source i).1)) ∧
      c.getVert (i.1 + 1) ∈
        ((Finset.univ.erase (source i).1).erase (rootMate (source i).1)))
    (i : Fin c.length)
    (hab : oneHighRootPair (branchLabel (c.getVert i.1)) ≠
      oneHighRootPair (branchLabel
        (c.getVert (oneHighCycleNext c hc i).1)))
    (hbc : oneHighRootPair (branchLabel
        (c.getVert (oneHighCycleNext c hc i).1)) ≠
      oneHighRootPair (branchLabel
        (c.getVert (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1)))
    (hac : oneHighRootPair (branchLabel (c.getVert i.1)) ≠
      oneHighRootPair (branchLabel
        (c.getVert (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1))) :
    (source i).1 = (source (oneHighCycleNext c hc i)).1 ∨
      (source i).1 = rootMate (source (oneHighCycleNext c hc i)).1 ∨
      oneHighRootPair (branchLabel (source i).1) =
        oneHighRootPair (branchLabel
          (c.getVert (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1)) ∨
      oneHighRootPair
          (branchLabel (source (oneHighCycleNext c hc i)).1) =
        oneHighRootPair (branchLabel (c.getVert i.1)) := by
  have hturn := oneHigh_sourceColoring_cyclic_turn_trichotomy
    G v rootMate branchLabel hbranchMate hc source hfar i hab hbc hac
  rcases oneHigh_sourcePair_turn_fourWay rootMate branchLabel hbranchMate
      (c.getVert i.1)
      (c.getVert (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1)
      (source i).1 (source (oneHighCycleNext c hc i)).1 hturn with
    heq | hmate | hleft | hright
  · exact Or.inl heq
  · exact Or.inr (Or.inl hmate)
  · exact Or.inr (Or.inr (Or.inl hleft))
  · exact Or.inr (Or.inr (Or.inr hright))

end

end Erdos85
