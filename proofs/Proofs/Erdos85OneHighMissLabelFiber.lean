import Proofs.Erdos85OneHighGlobalMissLabelCounting

/-! # Matched miss-label fibers

The unique-miss label carried by a matched vertex has exactly the graph-side
miss-count fiber.  This is the bridge from column parity of the miss table to
parity of endpoint labels in the global internal matching.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- In one source branch, matched vertices whose unique miss is `u` are
counted by the directed high-branch miss entry from `s` to `u`. -/
theorem card_oneHighMatchedMissLabelFiber_eq_highBranchMissCount
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (s u : {z : V // z ∈ G.neighborSet v})
    (hu : u ∈ ((Finset.univ.erase s).erase (rootMate s))) :
    ((Finset.univ : Finset (OneHighMatchedBranchVertices G v s)).filter
      fun x => oneHighMatchedMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj s x = u).card =
      highBranchMissCount G v s u := by
  classical
  let A := (Finset.univ : Finset (OneHighMatchedBranchVertices G v s)).filter
    fun x => oneHighMatchedMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj s x = u
  let B := (secondLayerBranch G v s).filter fun a =>
    (G.neighborFinset a ∩ secondLayerBranch G v u).card = 0
  change A.card = B.card
  apply Finset.card_bij (fun x _ => x.1.1)
  · intro x hx
    have hxparts := Finset.mem_filter.mp hx
    have hmiss := oneHighMatchedMissLabel_mem G hfree hv hexternal
      houterDegree rootMate hrootAdj s x
    have huMiss : u ∈ oneHighFarMissBranches G v rootMate s x.1.1 := by
      rw [← hxparts.2]
      exact hmiss
    exact Finset.mem_filter.mpr ⟨x.1.2, (Finset.mem_filter.mp huMiss).2⟩
  · intro x hx y hy hxy
    exact Subtype.ext (Subtype.ext hxy)
  · intro a ha
    have haParts := Finset.mem_filter.mp ha
    have haSecond : a ∈ secondLayer G v := by
      rw [secondLayer]
      exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, haParts.1⟩
    have hmissMem : u ∈ oneHighFarMissBranches G v rootMate s a := by
      exact Finset.mem_filter.mpr ⟨hu, haParts.2⟩
    have hmissPos : 0 < (oneHighFarMissBranches G v rootMate s a).card :=
      Finset.card_pos.mpr ⟨u, hmissMem⟩
    have hcount := card_farBranch_misses_eq_internalDegree
      G hfree (d := 7) (by omega) hexternal s (rootMate s)
        (hrootAdj s) a haParts.1 (houterDegree haSecond)
    have hcount' : (oneHighFarMissBranches G v rootMate s a).card =
        (G.neighborFinset a ∩ secondLayerBranch G v s).card := by
      simpa [oneHighFarMissBranches] using hcount
    have hinternalLe :
        (G.neighborFinset a ∩ secondLayerBranch G v s).card ≤ 1 := by
      have hdeg := degree_induce_secondLayerBranch_le_one
        G hfree v s ⟨a, haParts.1⟩
      rw [degree_induce_secondLayerBranch_eq_card_inter] at hdeg
      exact hdeg
    have hmatched :
        (G.neighborFinset a ∩ secondLayerBranch G v s).card = 1 := by
      omega
    let x : OneHighMatchedBranchVertices G v s := ⟨⟨a, haParts.1⟩, by
      rw [degree_induce_secondLayerBranch_eq_card_inter]
      exact hmatched⟩
    have hlabel : oneHighMatchedMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj s x = u := by
      symm
      exact eq_oneHighMissingBranch_of_matched_of_mem G hfree hv hexternal
        houterDegree rootMate hrootAdj s a haParts.1 hmatched u hmissMem
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlabel⟩, rfl⟩

/-- A global miss-label fiber is the disjoint sigma-sum of its source-branch
fibers.  This separates the purely dependent-type bookkeeping from the graph
identity above. -/
theorem card_oneHighGlobalMissLabelFiber_eq_sum_branchFibers
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (u : {z : V // z ∈ G.neighborSet v}) :
    ((Finset.univ : Finset (OneHighAllMatchedVertices G v)).filter
      fun x => oneHighGlobalMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj x = u).card =
      ∑ s : {z : V // z ∈ G.neighborSet v},
        ((Finset.univ : Finset (OneHighMatchedBranchVertices G v s)).filter
          fun x => oneHighMatchedMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj s x = u).card := by
  classical
  let A := {x : OneHighAllMatchedVertices G v //
    oneHighGlobalMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj x = u}
  let B := Σ s : {z : V // z ∈ G.neighborSet v},
    {x : OneHighMatchedBranchVertices G v s //
      oneHighMatchedMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj s x = u}
  let e : A ≃ B :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by cases x; rfl }
  calc
    ((Finset.univ : Finset (OneHighAllMatchedVertices G v)).filter
        fun x => oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj x = u).card = Fintype.card A := by
      simpa [A] using (Fintype.card_subtype (fun x :
        OneHighAllMatchedVertices G v =>
          oneHighGlobalMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj x = u)).symm
    _ = Fintype.card B := Fintype.card_congr e
    _ = ∑ s : {z : V // z ∈ G.neighborSet v},
        ((Finset.univ : Finset (OneHighMatchedBranchVertices G v s)).filter
          fun x => oneHighMatchedMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj s x = u).card := by
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro s _
      simpa using (Fintype.card_subtype (fun x :
        OneHighMatchedBranchVertices G v s =>
          oneHighMatchedMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj s x = u))

end

end Erdos85
