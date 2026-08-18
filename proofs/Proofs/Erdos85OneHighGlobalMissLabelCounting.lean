import Proofs.Erdos85OneHighGraphMissLabelCounting

/-! # Global profile-parametric miss-label counting -/

namespace Erdos85

noncomputable section

/-- All internally matched outer vertices, retaining their source branch. -/
abbrev OneHighAllMatchedVertices
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :=
  Σ s : {z : V // z ∈ G.neighborSet v},
    OneHighMatchedBranchVertices G v s

noncomputable instance oneHighAllMatchedVertices_linearOrder
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    LinearOrder (OneHighAllMatchedVertices G v) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- The global internal matching acts within each source-branch fiber. -/
noncomputable def oneHighGlobalInternalMate
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V) :
    OneHighAllMatchedVertices G v → OneHighAllMatchedVertices G v :=
  fun x => ⟨x.1, oneHighInternalMate G hfree v x.1 x.2⟩

theorem oneHighGlobalInternalMate_involutive
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V) :
    Function.Involutive (oneHighGlobalInternalMate G hfree v) := by
  rintro ⟨s, x⟩
  change Sigma.mk s (oneHighInternalMate G hfree v s
    (oneHighInternalMate G hfree v s x)) = Sigma.mk s x
  congr 1
  exact degreeOneMate_involutive _ _ x

theorem oneHighGlobalInternalMate_ne
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (x : OneHighAllMatchedVertices G v) :
    oneHighGlobalInternalMate G hfree v x ≠ x := by
  rcases x with ⟨s, x⟩
  change Sigma.mk s (oneHighInternalMate G hfree v s x) ≠ Sigma.mk s x
  intro h
  injection h with _ hfiber
  exact degreeOneMate_ne _ _ x hfiber

/-- The global miss label uses the source branch stored in the sigma. -/
noncomputable def oneHighGlobalMissLabel
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1) :
    OneHighAllMatchedVertices G v →
      {z : V // z ∈ G.neighborSet v} :=
  fun x => oneHighMatchedMissLabel G hfree hv hexternal houterDegree
    rootMate hrootAdj x.1 x.2

theorem oneHighGlobalMissLabel_mem
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
    oneHighGlobalMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj x ∈
      oneHighFarMissBranches G v rootMate x.1 x.2.1.1 := by
  exact oneHighMatchedMissLabel_mem G hfree hv hexternal houterDegree
    rootMate hrootAdj x.1 x.2

theorem card_oneHighMatchedBranchVertices_eq_highBranchMatchedCount
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s : {z : V // z ∈ G.neighborSet v}) :
    Fintype.card (OneHighMatchedBranchVertices G v s) =
      highBranchMatchedCount G v s := by
  classical
  rw [highBranchMatchedCount]
  let B := secondLayerBranch G v s
  let H := G.induce B
  change Fintype.card {x : B // H.degree x = 1} = _
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  exact
    { toFun := fun x => ⟨x.1.1, Finset.mem_filter.mpr ⟨x.1.2, by
          rw [← degree_induce_secondLayerBranch_eq_card_inter]
          exact x.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (Finset.mem_filter.mp x.2).1⟩, by
          rw [degree_induce_secondLayerBranch_eq_card_inter]
          exact (Finset.mem_filter.mp x.2).2⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by cases x; rfl }

theorem card_oneHighAllMatchedVertices_eq_sum
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Fintype.card (OneHighAllMatchedVertices G v) =
      ∑ s : {z : V // z ∈ G.neighborSet v}, highBranchMatchedCount G v s := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact card_oneHighMatchedBranchVertices_eq_highBranchMatchedCount G v s

/-- The literal family word has `32 - 2*a` matched outer vertices. -/
theorem sum_two_mul_oneHighFamilyInternalEdges
    (a : Nat) (ha : a ≤ 4) :
    (∑ i : Fin 8, 2 * oneHighFamilyInternalEdges a i) = 32 - 2 * a := by
  interval_cases a <;> decide

/-- Exact profile-parametric global cardinality.  In particular profiles
`AAAA, AAAB, AABB, ABBB, BBBB` have `24,26,28,30,32` matched vertices. -/
theorem card_oneHighAllMatchedVertices_eq_profile
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (a : Nat) (ha : a ≤ 4)
    (hIN : ∀ i, highBranchMatchedCount G v (branchLabel.symm i) =
      2 * oneHighFamilyInternalEdges a i) :
    Fintype.card (OneHighAllMatchedVertices G v) = 32 - 2 * a := by
  rw [card_oneHighAllMatchedVertices_eq_sum]
  rw [← Equiv.sum_comp branchLabel.symm]
  simp_rw [hIN]
  exact sum_two_mul_oneHighFamilyInternalEdges a ha

/-- Exact global multiplicity accounting, together with the graph facts
which make its labels genuine unique misses.  This intentionally states no
unjustified repeated-key conclusion: there are 28 ambient unordered root
pairs but only 12--16 internal matching edges. -/
theorem oneHigh_global_nonconstantMiss_counting_package
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1) :
    let X := OneHighAllMatchedVertices G v
    let mate := oneHighGlobalInternalMate G hfree v
    let label := oneHighGlobalMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj
    Function.Involutive mate ∧
      (∀ x, mate x ≠ x) ∧
      (∀ x, label x ∈ oneHighFarMissBranches G v rootMate x.1 x.2.1.1) ∧
      (∑ key ∈ exchangedMissPairKeys
          {z : V // z ∈ G.neighborSet v},
        exchangedMissPairMultiplicity mate label key) =
        (nonconstantMatchingEdgeSources mate label).card := by
  classical
  dsimp
  refine ⟨oneHighGlobalInternalMate_involutive G hfree v,
    oneHighGlobalInternalMate_ne G hfree v, ?_, ?_⟩
  · exact oneHighGlobalMissLabel_mem G hfree hv hexternal houterDegree
      rootMate hrootAdj
  · exact sum_exchangedMissPairMultiplicity_over_keys _ _

end

end Erdos85
