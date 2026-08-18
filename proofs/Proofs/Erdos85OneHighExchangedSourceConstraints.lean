import Proofs.Erdos85OneHighMissLabelFiber

/-! # Source constraints on exchanged miss keys

Every internal matching edge stays inside one source branch.  Both miss labels
on that edge therefore lie among the source's far root branches.  This records
the source-color data needed when the Eulerian odd-key cycle is split into
structural repeated-source and certificate-backed proper-color sectors.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Both endpoint miss labels of a global internal matching edge are far from
its source root and the source root's mate. -/
theorem oneHighGlobalMissLabels_mem_sourceFarBranches
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (x : OneHighAllMatchedVertices G v) :
    let mate := oneHighGlobalInternalMate G hfree v
    let label := oneHighGlobalMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj
    label x ∈ ((Finset.univ.erase x.1).erase (rootMate x.1)) ∧
      label (mate x) ∈ ((Finset.univ.erase x.1).erase (rootMate x.1)) := by
  dsimp only
  constructor
  · exact (Finset.mem_filter.mp (oneHighGlobalMissLabel_mem G hfree hv
      hexternal houterDegree rootMate hrootAdj x)).1
  · have hmem := oneHighGlobalMissLabel_mem G hfree hv hexternal
      houterDegree rootMate hrootAdj
        (oneHighGlobalInternalMate G hfree v x)
    exact (Finset.mem_filter.mp hmem).1

/-- Consequently the two canonically ordered endpoints of every exchanged
miss key lie in the same source-far set. -/
theorem oneHigh_exchangedMissPairKey_mem_sourceFarBranches
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (x : OneHighAllMatchedVertices G v) :
    let mate := oneHighGlobalInternalMate G hfree v
    let label := oneHighGlobalMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj
    (exchangedMissPairKey mate label x).1 ∈
        ((Finset.univ.erase x.1).erase (rootMate x.1)) ∧
      (exchangedMissPairKey mate label x).2 ∈
        ((Finset.univ.erase x.1).erase (rootMate x.1)) := by
  dsimp only
  have hlabels := oneHighGlobalMissLabels_mem_sourceFarBranches G hfree hv
    hexternal houterDegree rootMate hrootAdj x
  unfold exchangedMissPairKey
  by_cases hle :
      oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj x ≤
        oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj (oneHighGlobalInternalMate G hfree v x)
  · simpa [min_eq_left hle, max_eq_right hle] using hlabels
  · have hle' :
        oneHighGlobalMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj (oneHighGlobalInternalMate G hfree v x) ≤
          oneHighGlobalMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj x := le_of_not_ge hle
    simpa [min_eq_right hle', max_eq_left hle'] using hlabels.symm

/-- Positive exchanged-key multiplicity supplies an actual canonically
oriented matching edge carrying that key. -/
theorem exists_source_of_exchangedMissPairMultiplicity_pos
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) (key : L × L)
    (hpos : 0 < exchangedMissPairMultiplicity mate label key) :
    ∃ x ∈ nonconstantMatchingEdgeSources mate label,
      exchangedMissPairKey mate label x = key := by
  unfold exchangedMissPairMultiplicity at hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

/-- Every positive-multiplicity global exchanged key admits a concrete
source-branch color, and both key endpoints obey that source's far constraint.
This is the witness interface used to color edges of the odd label support. -/
theorem exists_sourceColor_of_oneHigh_exchangedMultiplicity_pos
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (key : {z : V // z ∈ G.neighborSet v} ×
      {z : V // z ∈ G.neighborSet v})
    (hpos : 0 < exchangedMissPairMultiplicity
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj) key) :
    ∃ x : OneHighAllMatchedVertices G v,
      x ∈ nonconstantMatchingEdgeSources
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj) ∧
      exchangedMissPairKey
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj) x = key ∧
      key.1 ∈ ((Finset.univ.erase x.1).erase (rootMate x.1)) ∧
      key.2 ∈ ((Finset.univ.erase x.1).erase (rootMate x.1)) := by
  obtain ⟨x, hx, hkey⟩ := exists_source_of_exchangedMissPairMultiplicity_pos
    (oneHighGlobalInternalMate G hfree v)
    (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj) key hpos
  have hfar := oneHigh_exchangedMissPairKey_mem_sourceFarBranches G hfree hv
    hexternal houterDegree rootMate hrootAdj x
  exact ⟨x, hx, hkey, hkey ▸ hfar⟩

end

end Erdos85
