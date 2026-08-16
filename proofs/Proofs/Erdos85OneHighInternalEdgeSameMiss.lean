import Proofs.Erdos85BranchDeficitSymmetry

/-! # Local propagation toward the one-high same-miss lemma -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- In a `C₄`-free graph, the opposite endpoints of two edges leaving an
internal edge cannot themselves be adjacent. -/
theorem not_adj_of_internalEdge_crossEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {x y a b : V} (hxb : x ≠ b) (hay : a ≠ y)
    (hxy : G.Adj x y) (hxa : G.Adj x a) (hyb : G.Adj y b) :
    ¬ G.Adj a b := by
  intro hab
  have hle := common_le_one_of_not_containsC4 hfree x b hxb
  have hyCommon : y ∈ G.neighborFinset x ∩ G.neighborFinset b := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxy, hyb.symm⟩
  have haCommon : a ∈ G.neighborFinset x ∩ G.neighborFinset b := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxa, hab.symm⟩
  exact hay (Finset.card_le_one.mp hle a haCommon y hyCommon)

/-- Branch-specialized form: if adjacent vertices of one second-layer branch
both hit a distinct branch, their chosen cross-neighbors form a nonedge.
This is the local propagation constraint needed when analyzing a hypothetical
failure of the internal-edge same-miss property. -/
theorem not_adj_crossTargets_of_internalEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (s u : {z : V // z ∈ G.neighborSet v}) (hsu : s ≠ u)
    {x y a b : V}
    (hxs : x ∈ secondLayerBranch G v s)
    (hys : y ∈ secondLayerBranch G v s)
    (hau : a ∈ secondLayerBranch G v u)
    (hbu : b ∈ secondLayerBranch G v u)
    (hxy : G.Adj x y) (hxa : G.Adj x a) (hyb : G.Adj y b) :
    ¬ G.Adj a b := by
  have hdisj : Disjoint (secondLayerBranch G v s)
      (secondLayerBranch G v u) :=
    secondLayerBranch_pairwiseDisjoint G hfree v
      (by simp) (by simp) hsu
  have hxb : x ≠ b := by
    intro h
    subst b
    exact (Finset.disjoint_left.mp hdisj hxs hbu)
  have hay : a ≠ y := by
    intro h
    subst a
    exact (Finset.disjoint_left.mp hdisj hys hau)
  exact not_adj_of_internalEdge_crossEdges G hfree hxb hay hxy hxa hyb

/-- If both endpoints of an internal branch edge hit a fixed far branch,
there are cross-neighbors in that branch which are forced to be nonadjacent.
Thus any proof of same-miss may treat a failure as a rigid nonedge in every
common-hit target branch. -/
theorem exists_nonadjacent_crossTargets_of_internalEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (s u : {z : V // z ∈ G.neighborSet v}) (hsu : s ≠ u)
    {x y : V}
    (hxs : x ∈ secondLayerBranch G v s)
    (hys : y ∈ secondLayerBranch G v s)
    (hxy : G.Adj x y)
    (hxHit : (G.neighborFinset x ∩ secondLayerBranch G v u).card ≠ 0)
    (hyHit : (G.neighborFinset y ∩ secondLayerBranch G v u).card ≠ 0) :
    ∃ a b : V,
      a ∈ secondLayerBranch G v u ∧
      b ∈ secondLayerBranch G v u ∧
      G.Adj x a ∧ G.Adj y b ∧ ¬ G.Adj a b := by
  have hxNonempty :
      (G.neighborFinset x ∩ secondLayerBranch G v u).Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hyNonempty :
      (G.neighborFinset y ∩ secondLayerBranch G v u).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨a, ha⟩ := hxNonempty
  obtain ⟨b, hb⟩ := hyNonempty
  have haParts := Finset.mem_inter.mp ha
  have hbParts := Finset.mem_inter.mp hb
  refine ⟨a, b, haParts.2, hbParts.2, ?_, ?_, ?_⟩
  · exact (G.mem_neighborFinset x a).mp haParts.1
  · exact (G.mem_neighborFinset y b).mp hbParts.1
  · exact not_adj_crossTargets_of_internalEdge G hfree s u hsu
      hxs hys haParts.2 hbParts.2 hxy
      ((G.mem_neighborFinset x a).mp haParts.1)
      ((G.mem_neighborFinset y b).mp hbParts.1)

/-- A failure of same-miss across an internal edge is necessarily an
exchange: the second endpoint has a unique missed far branch different from
`u`, and the first endpoint hits that branch.  This reduces the hard case to
alternating pairs of miss labels rather than arbitrary row discrepancies. -/
theorem exists_exchangedMiss_of_internalEdge_not_sameMiss
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} {v : V}
    (hv : G.degree v = d + 1)
    (hexternal : externalRepairCandidates G v = ∅)
    (s t u : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1)
    (hu : u ∈ ((Finset.univ.erase s).erase t))
    {x y : V}
    (hxs : x ∈ secondLayerBranch G v s)
    (hys : y ∈ secondLayerBranch G v s)
    (hxy : G.Adj x y)
    (hxdegree : G.degree x = d) (hydegree : G.degree y = d)
    (hxMiss : (G.neighborFinset x ∩ secondLayerBranch G v u).card = 0)
    (hyHit : (G.neighborFinset y ∩ secondLayerBranch G v u).card ≠ 0) :
    ∃ w ∈ ((Finset.univ.erase s).erase t),
      w ≠ u ∧
      (G.neighborFinset y ∩ secondLayerBranch G v w).card = 0 ∧
      (G.neighborFinset x ∩ secondLayerBranch G v w).card ≠ 0 := by
  classical
  let F := (Finset.univ.erase s).erase t
  let missX := F.filter fun w =>
    (G.neighborFinset x ∩ secondLayerBranch G v w).card = 0
  let missY := F.filter fun w =>
    (G.neighborFinset y ∩ secondLayerBranch G v w).card = 0
  have hxsne : x ≠ s.1 := by
    intro h
    subst x
    exact (Finset.mem_sdiff.mp hxs).2 (by
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr s.2)
  have hysne : y ≠ s.1 := by
    intro h
    subst y
    exact (Finset.mem_sdiff.mp hys).2 (by
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr s.2)
  have hxInternalLe := card_neighborFinset_inter_secondLayerBranch_le_one
    G hfree v x s hxsne
  have hyInternalLe := card_neighborFinset_inter_secondLayerBranch_le_one
    G hfree v y s hysne
  have hxInternalPos :
      0 < (G.neighborFinset x ∩ secondLayerBranch G v s).card := by
    rw [Finset.card_pos]
    exact ⟨y, Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x y).mpr hxy, hys⟩⟩
  have hyInternalPos :
      0 < (G.neighborFinset y ∩ secondLayerBranch G v s).card := by
    rw [Finset.card_pos]
    exact ⟨x, Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset y x).mpr hxy.symm, hxs⟩⟩
  have hxInternal :
      (G.neighborFinset x ∩ secondLayerBranch G v s).card = 1 := by
    omega
  have hyInternal :
      (G.neighborFinset y ∩ secondLayerBranch G v s).card = 1 := by
    omega
  have hmissX : missX.card = 1 := by
    simpa [F, missX, hxInternal] using
      card_farBranch_misses_eq_internalDegree
        G hfree hv hexternal s t hst x hxs hxdegree
  have hmissY : missY.card = 1 := by
    simpa [F, missY, hyInternal] using
      card_farBranch_misses_eq_internalDegree
        G hfree hv hexternal s t hst y hys hydegree
  have huX : u ∈ missX := by
    exact Finset.mem_filter.mpr ⟨by simpa [F] using hu, hxMiss⟩
  have huNotY : u ∉ missY := by
    intro hum
    exact hyHit (Finset.mem_filter.mp hum).2
  obtain ⟨w, hwY⟩ := Finset.card_pos.mp (by omega : 0 < missY.card)
  have hwParts := Finset.mem_filter.mp hwY
  have hwu : w ≠ u := by
    intro h
    subst w
    exact huNotY hwY
  have hwNotX : w ∉ missX := by
    intro hwX
    have := Finset.card_le_one.mp (by omega : missX.card ≤ 1)
      w hwX u huX
    exact hwu this
  refine ⟨w, by simpa [F] using hwParts.1, hwu, hwParts.2, ?_⟩
  intro hxZero
  exact hwNotX (Finset.mem_filter.mpr ⟨hwParts.1, hxZero⟩)

end

end Erdos85
