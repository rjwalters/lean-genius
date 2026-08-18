import Proofs.Erdos85OneHighOddLabelEdgeSource
import Proofs.Erdos85OneHighRootPairDecoder
import Proofs.Erdos85OddLabelCycleLength

/-! # Source colors along an odd label-support cycle -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Cyclic successor on the dart indices of a genuine cycle. -/
def oneHighCycleNext
    {L : Type*} {H : SimpleGraph L} {l : L} (c : H.Walk l l)
    (hc : c.IsCycle) (i : Fin c.length) : Fin c.length :=
  ⟨(i.1 + 1) % c.length, Nat.mod_lt _ (by
    have := hc.three_le_length
    omega)⟩

/-- The cyclic successor index denotes the literal next walk vertex; at the
last dart this identifies `getVert length` with the initial vertex. -/
theorem getVert_oneHighCycleNext
    {L : Type*} {H : SimpleGraph L} {l : L} (c : H.Walk l l)
    (hc : c.IsCycle) (i : Fin c.length) :
    c.getVert (oneHighCycleNext c hc i).1 = c.getVert (i.1 + 1) := by
  by_cases hnext : i.1 + 1 < c.length
  · simp [oneHighCycleNext, Nat.mod_eq_of_lt hnext]
  · have hlast : i.1 + 1 = c.length := by omega
    simp [oneHighCycleNext, hlast]

/-- Every dart of an odd label-support cycle can be decorated by a concrete
nonconstant internal matching-edge source.  The decoration retains its exact
exchanged key and the two graph-side far constraints. -/
theorem exists_sourceColoring_of_oneHigh_oddLabelCycle
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {x : V}, x ∈ secondLayer G v → G.degree x = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    {l : {z : V // z ∈ G.neighborSet v}}
    {c : (oddExchangedKeyLabelGraph
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj))).Walk l l}
    (_hc : c.IsCycle) :
    ∃ source : Fin c.length → OneHighAllMatchedVertices G v,
      ∀ i : Fin c.length,
        source i ∈ nonconstantMatchingEdgeSources
          (oneHighGlobalInternalMate G hfree v)
          (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj) ∧
        exchangedMissPairKey
          (oneHighGlobalInternalMate G hfree v)
          (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj) (source i) =
          (min (c.getVert i.1) (c.getVert (i.1 + 1)),
            max (c.getVert i.1) (c.getVert (i.1 + 1))) ∧
        c.getVert i.1 ∈
          ((Finset.univ.erase (source i).1).erase (rootMate (source i).1)) ∧
        c.getVert (i.1 + 1) ∈
          ((Finset.univ.erase (source i).1).erase (rootMate (source i).1)) := by
  classical
  have hedge : ∀ i : Fin c.length,
      (oddExchangedKeyLabelGraph
        (exchangedMissPairMultiplicity
          (oneHighGlobalInternalMate G hfree v)
          (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj))).Adj
        (c.getVert i.1) (c.getVert (i.1 + 1)) := by
    intro i
    exact c.adj_getVert_succ i.2
  have hex : ∀ i : Fin c.length,
      ∃ x : OneHighAllMatchedVertices G v,
        x ∈ nonconstantMatchingEdgeSources
          (oneHighGlobalInternalMate G hfree v)
          (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj) ∧
        exchangedMissPairKey
          (oneHighGlobalInternalMate G hfree v)
          (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj) x =
          (min (c.getVert i.1) (c.getVert (i.1 + 1)),
            max (c.getVert i.1) (c.getVert (i.1 + 1))) ∧
        c.getVert i.1 ∈
          ((Finset.univ.erase x.1).erase (rootMate x.1)) ∧
        c.getVert (i.1 + 1) ∈
          ((Finset.univ.erase x.1).erase (rootMate x.1)) := by
    intro i
    exact exists_sourceColor_of_oneHigh_oddLabelEdge G hfree hv hexternal
      houterDegree rootMate hrootAdj (hedge i)
  choose source hsource using hex
  exact ⟨source, hsource⟩

/-- At every interior turn of a source-colored label cycle whose three label
mate-pairs are distinct, the adjacent source-pair colors satisfy the exact
four-color trichotomy. -/
theorem oneHigh_sourceColoring_turn_trichotomy
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s, branchLabel (rootMate s) =
      oneHighStandardMate (branchLabel s))
    {H : SimpleGraph {z : V // z ∈ G.neighborSet v}}
    {l : {z : V // z ∈ G.neighborSet v}} (c : H.Walk l l)
    (source : Fin c.length → OneHighAllMatchedVertices G v)
    (hfar : ∀ i : Fin c.length,
      c.getVert i.1 ∈
        ((Finset.univ.erase (source i).1).erase (rootMate (source i).1)) ∧
      c.getVert (i.1 + 1) ∈
        ((Finset.univ.erase (source i).1).erase (rootMate (source i).1)))
    (i : ℕ) (hi : i + 2 ≤ c.length)
    (hab : oneHighRootPair (branchLabel (c.getVert i)) ≠
      oneHighRootPair (branchLabel (c.getVert (i + 1))))
    (hbc : oneHighRootPair (branchLabel (c.getVert (i + 1))) ≠
      oneHighRootPair (branchLabel (c.getVert (i + 2))))
    (hac : oneHighRootPair (branchLabel (c.getVert i)) ≠
      oneHighRootPair (branchLabel (c.getVert (i + 2)))) :
    let ei : Fin c.length := ⟨i, by omega⟩
    let ej : Fin c.length := ⟨i + 1, by omega⟩
    oneHighRootPair (branchLabel (source ei).1) =
        oneHighRootPair (branchLabel (source ej).1) ∨
      oneHighRootPair (branchLabel (source ei).1) =
        oneHighRootPair (branchLabel (c.getVert (i + 2))) ∨
      oneHighRootPair (branchLabel (source ej).1) =
        oneHighRootPair (branchLabel (c.getVert i)) := by
  dsimp only
  let ei : Fin c.length := ⟨i, by omega⟩
  let ej : Fin c.length := ⟨i + 1, by omega⟩
  have hif := hfar ei
  have hjf := hfar ej
  have hsa := oneHighRootPair_ne_of_branch_mem_far rootMate branchLabel
    hbranchMate (source ei).1 (c.getVert i) hif.1
  have hsb := oneHighRootPair_ne_of_branch_mem_far rootMate branchLabel
    hbranchMate (source ei).1 (c.getVert (i + 1)) hif.2
  have htb := oneHighRootPair_ne_of_branch_mem_far rootMate branchLabel
    hbranchMate (source ej).1 (c.getVert (i + 1)) hjf.1
  have htc := oneHighRootPair_ne_of_branch_mem_far rootMate branchLabel
    hbranchMate (source ej).1 (c.getVert (i + 2)) hjf.2
  exact oneHigh_sourcePair_turn_trichotomy
    (branchLabel (c.getVert i))
    (branchLabel (c.getVert (i + 1)))
    (branchLabel (c.getVert (i + 2)))
    (branchLabel (source ei).1) (branchLabel (source ej).1)
    hab hbc hac hsa hsb htb htc

/-- Re-express the second far endpoint of each colored dart using the cyclic
successor index. -/
theorem oneHigh_sourceColoring_far_next
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    {H : SimpleGraph {z : V // z ∈ G.neighborSet v}}
    {l : {z : V // z ∈ G.neighborSet v}} {c : H.Walk l l}
    (hc : c.IsCycle)
    (source : Fin c.length → OneHighAllMatchedVertices G v)
    (hfar : ∀ i : Fin c.length,
      c.getVert i.1 ∈
        ((Finset.univ.erase (source i).1).erase (rootMate (source i).1)) ∧
      c.getVert (i.1 + 1) ∈
        ((Finset.univ.erase (source i).1).erase (rootMate (source i).1)))
    (i : Fin c.length) :
    c.getVert (oneHighCycleNext c hc i).1 ∈
      ((Finset.univ.erase (source i).1).erase (rootMate (source i).1)) := by
  rw [getVert_oneHighCycleNext c hc i]
  exact (hfar i).2

/-- Uniform cyclic turn classifier, including the two turns crossing the
chosen start/end of the walk representation. -/
theorem oneHigh_sourceColoring_cyclic_turn_trichotomy
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
    oneHighRootPair (branchLabel (source i).1) =
        oneHighRootPair (branchLabel (source (oneHighCycleNext c hc i)).1) ∨
      oneHighRootPair (branchLabel (source i).1) =
        oneHighRootPair (branchLabel
          (c.getVert (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1)) ∨
      oneHighRootPair (branchLabel (source (oneHighCycleNext c hc i)).1) =
        oneHighRootPair (branchLabel (c.getVert i.1)) := by
  let j := oneHighCycleNext c hc i
  let k := oneHighCycleNext c hc j
  have hif := hfar i
  have hjf := hfar j
  have hsa := oneHighRootPair_ne_of_branch_mem_far rootMate branchLabel
    hbranchMate (source i).1 (c.getVert i.1) hif.1
  have hsb := oneHighRootPair_ne_of_branch_mem_far rootMate branchLabel
    hbranchMate (source i).1 (c.getVert j.1)
      (oneHigh_sourceColoring_far_next G v rootMate hc source hfar i)
  have htb := oneHighRootPair_ne_of_branch_mem_far rootMate branchLabel
    hbranchMate (source j).1 (c.getVert j.1) hjf.1
  have htc := oneHighRootPair_ne_of_branch_mem_far rootMate branchLabel
    hbranchMate (source j).1 (c.getVert k.1)
      (oneHigh_sourceColoring_far_next G v rootMate hc source hfar j)
  exact oneHigh_sourcePair_turn_trichotomy
    (branchLabel (c.getVert i.1)) (branchLabel (c.getVert j.1))
    (branchLabel (c.getVert k.1))
    (branchLabel (source i).1) (branchLabel (source j).1)
    hab hbc hac hsa hsb htb htc

end

end Erdos85
