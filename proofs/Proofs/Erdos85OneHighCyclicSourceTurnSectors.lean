import Proofs.Erdos85OneHighCyclicSourceTurnRefinement
import Proofs.Erdos85OneHighDistinctTurnSources

/-! # Graph-ready sectors at a cyclic source-colored turn -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The exact cyclic source-turn split, with the same-branch sector upgraded
to two distinct canonical internal matching-edge sources. -/
theorem oneHigh_sourceColoring_cyclic_turn_fourWay_distinct
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
    (mate : OneHighAllMatchedVertices G v → OneHighAllMatchedVertices G v)
    (label : OneHighAllMatchedVertices G v →
      {z : V // z ∈ G.neighborSet v})
    (source : Fin c.length → OneHighAllMatchedVertices G v)
    (hkey : ∀ i : Fin c.length,
      exchangedMissPairKey mate label (source i) =
        (min (c.getVert i.1) (c.getVert (i.1 + 1)),
          max (c.getVert i.1) (c.getVert (i.1 + 1))))
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
    ((source i).1 = (source (oneHighCycleNext c hc i)).1 ∧
      source i ≠ source (oneHighCycleNext c hc i)) ∨
      (source i).1 = rootMate (source (oneHighCycleNext c hc i)).1 ∨
      oneHighRootPair (branchLabel (source i).1) =
        oneHighRootPair (branchLabel
          (c.getVert (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1)) ∨
      oneHighRootPair
          (branchLabel (source (oneHighCycleNext c hc i)).1) =
        oneHighRootPair (branchLabel (c.getVert i.1)) := by
  have habv : c.getVert i.1 ≠
      c.getVert (oneHighCycleNext c hc i).1 := by
    intro h
    apply hab
    rw [h]
  have hbcv : c.getVert (oneHighCycleNext c hc i).1 ≠
      c.getVert
        (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1 := by
    intro h
    apply hbc
    rw [h]
  have hacv : c.getVert i.1 ≠
      c.getVert
        (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1 := by
    intro h
    apply hac
    rw [h]
  have hsne := oneHigh_sourceColoring_cyclic_turn_sources_ne
    G v hc mate label source hkey i habv hbcv hacv
  rcases oneHigh_sourceColoring_cyclic_turn_fourWay
      G v rootMate branchLabel hbranchMate hc source hfar i hab hbc hac with
    hsame | hmate | hleft | hright
  · exact Or.inl ⟨hsame, hsne⟩
  · exact Or.inr (Or.inl hmate)
  · exact Or.inr (Or.inr (Or.inl hleft))
  · exact Or.inr (Or.inr (Or.inr hright))

end

end Erdos85
