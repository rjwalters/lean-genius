import Proofs.Erdos85OneHighOddProfilePartitionEscape

/-! # Forced escape for a specified partition edge-data witness -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The target escape derived from a local-edge witness can be tied to one
specified source edge and one specified target edge from its `edge_data`.
This is the coherent form needed when two target edges are later shown to
exhaust a two-edge branch. -/
theorem OneHighPartitionLocalEdgeWitness.exists_targetEscape_of_edgeData
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} {code : Fin 3}
    (q : OneHighPartitionLocalEdgeWitness G hfree hv p code)
    (key : OneHighLabelPair)
    (hkeylt : key.1 < key.2)
    (hkeyFarT : OneHighKeyFarFromSource key (p.branchLabel q.t))
    (x : OneHighMatchedBranchVertices G v q.s)
    (_hx : x ∈ matchingEdgeSources (oneHighInternalMate G hfree v q.s))
    (hxkey :
      (min (p.branchLabel (oneHighMatchedMissLabel G hfree hv
          p.external_empty p.outer_degree p.mate p.mate_adj q.s x))
          (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj q.s
              (oneHighInternalMate G hfree v q.s x))),
        max (p.branchLabel (oneHighMatchedMissLabel G hfree hv
          p.external_empty p.outer_degree p.mate p.mate_adj q.s x))
          (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj q.s
              (oneHighInternalMate G hfree v q.s x)))) = key)
    (y : OneHighMatchedBranchVertices G v q.t)
    (_hy : y ∈ matchingEdgeSources (oneHighInternalMate G hfree v q.t)) :
    ∃ a b : V,
      a ∈ secondLayerBranch G v q.t ∧
      b ∈ secondLayerBranch G v q.t ∧
      G.Adj x.1.1 a ∧
      G.Adj (oneHighInternalMate G hfree v q.s x).1.1 b ∧
      a ≠ b ∧ ¬ G.Adj a b ∧
      ((a ≠ y.1.1 ∧
          a ≠ (oneHighInternalMate G hfree v q.t y).1.1) ∨
        (b ≠ y.1.1 ∧
          b ≠ (oneHighInternalMate G hfree v q.t y).1.1)) := by
  let lx := p.branchLabel (oneHighMatchedMissLabel G hfree hv
    p.external_empty p.outer_degree p.mate p.mate_adj q.s x)
  let lxm := p.branchLabel (oneHighMatchedMissLabel G hfree hv
    p.external_empty p.outer_degree p.mate p.mate_adj q.s
      (oneHighInternalMate G hfree v q.s x))
  have hlne : lx ≠ lxm := by
    intro h
    have hfst := congrArg Prod.fst hxkey
    have hsnd := congrArg Prod.snd hxkey
    change min lx lxm = key.1 at hfst
    change max lx lxm = key.2 at hsnd
    rw [h, min_self] at hfst
    rw [h, max_self] at hsnd
    exact hkeylt.ne (hfst.symm.trans hsnd)
  have hkeyCanon : (min key.1 key.2, max key.1 key.2) = key := by
    simp [min_eq_left hkeylt.le, max_eq_right hkeylt.le]
  have hdecode : (lx = key.1 ∧ lxm = key.2) ∨
      (lx = key.2 ∧ lxm = key.1) := by
    apply eq_or_swap_of_minMax_pair_eq hlne hkeylt.ne
    exact hxkey.trans hkeyCanon.symm
  have hlxNeT : lx ≠ p.branchLabel q.t := by
    rcases hdecode with hdecode | hdecode
    · exact hdecode.1.symm ▸ hkeyFarT.1
    · exact hdecode.1.symm ▸ hkeyFarT.2.1
  have hlxmNeT : lxm ≠ p.branchLabel q.t := by
    rcases hdecode with hdecode | hdecode
    · exact hdecode.2.symm ▸ hkeyFarT.2.1
    · exact hdecode.2.symm ▸ hkeyFarT.1
  have htFar : q.t ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)) := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨q.target_ne_mate, q.source_ne.symm⟩
  have hxMissNeT : q.t ≠ oneHighMatchedMissLabel G hfree hv
      p.external_empty p.outer_degree p.mate p.mate_adj q.s x := by
    intro h
    apply hlxNeT
    exact congrArg p.branchLabel h.symm
  have hxmMissNeT : q.t ≠ oneHighMatchedMissLabel G hfree hv
      p.external_empty p.outer_degree p.mate p.mate_adj q.s
        (oneHighInternalMate G hfree v q.s x) := by
    intro h
    apply hlxmNeT
    exact congrArg p.branchLabel h.symm
  have hxHit : (G.neighborFinset x.1.1 ∩
      secondLayerBranch G v q.t).card ≠ 0 := by
    rw [oneHighMatchedVertex_hits_farBranch_of_ne_miss
      G hfree hv p q.s x q.t htFar hxMissNeT]
    omega
  have hxmHit : (G.neighborFinset
      (oneHighInternalMate G hfree v q.s x).1.1 ∩
      secondLayerBranch G v q.t).card ≠ 0 := by
    rw [oneHighMatchedVertex_hits_farBranch_of_ne_miss
      G hfree hv p q.s (oneHighInternalMate G hfree v q.s x)
        q.t htFar hxmMissNeT]
    omega
  have hxEdge : G.Adj x.1.1
      (oneHighInternalMate G hfree v q.s x).1.1 := by
    simpa [oneHighInternalMate] using degreeOneMate_adj
      (G.induce (secondLayerBranch G v q.s))
      (degree_induce_secondLayerBranch_le_one G hfree v q.s) x
  obtain ⟨a, b, ha, hb, hxa, hxmb, hnab⟩ :=
    exists_nonadjacent_crossTargets_of_internalEdge G hfree q.s q.t
      q.source_ne x.1.2 (oneHighInternalMate G hfree v q.s x).1.2
      hxEdge hxHit hxmHit
  have hxne : x.1.1 ≠ (oneHighInternalMate G hfree v q.s x).1.1 := by
    intro h
    apply degreeOneMate_ne (G.induce (secondLayerBranch G v q.s))
      (degree_induce_secondLayerBranch_le_one G hfree v q.s) x
    exact Subtype.ext (Subtype.ext h.symm)
  have hab : a ≠ b := ne_crossTargets_of_distinct_sourceVertices
    G hfree x.1.2 (oneHighInternalMate G hfree v q.s x).1.2 hxne
      ha hb hxa hxmb
  have hyEdge : G.Adj y.1.1
      (oneHighInternalMate G hfree v q.t y).1.1 := by
    simpa [oneHighInternalMate] using degreeOneMate_adj
      (G.induce (secondLayerBranch G v q.t))
      (degree_induce_secondLayerBranch_le_one G hfree v q.t) y
  have hescape := c4Free_secondLayerPartnerEdges_exists_target_escape
    G hfree q.source_ne x.1.2
      (oneHighInternalMate G hfree v q.s x).1.2 y.1.2
      (oneHighInternalMate G hfree v q.t y).1.2
      hxEdge hyEdge hxa hxmb hab
  exact ⟨a, b, ha, hb, hxa, hxmb, hab, hnab, hescape⟩

end

end Erdos85

#print axioms Erdos85.OneHighPartitionLocalEdgeWitness.exists_targetEscape_of_edgeData
