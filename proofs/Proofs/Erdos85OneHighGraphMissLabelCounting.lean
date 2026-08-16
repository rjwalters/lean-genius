import Proofs.Erdos85OneHighExchangedMissCounting
import Proofs.Erdos85OneHighCanonicalMate

/-! # Graph instantiation of exchanged miss-label counting

The abstract counting layer is instantiated on the degree-one vertices of a
single second-layer branch.  These vertices carry the intrinsic matching
involution, and pointwise dirty conservation supplies their unique far-branch
label.
-/

namespace Erdos85

noncomputable section

/-- The vertices of a graph which have degree exactly one. -/
abbrev DegreeOneVertices {X : Type*} [Fintype X] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj] :=
  {x : X // H.degree x = 1}

/-- The unique neighbor of a degree-one vertex, restricted back to the
degree-one vertices when every graph degree is at most one. -/
noncomputable def degreeOneMate
    {X : Type*} [Fintype X] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x ≤ 1) : DegreeOneVertices H → DegreeOneVertices H :=
  fun x => by
    have hn : H.neighborFinset x.1 |>.Nonempty :=
      Finset.card_pos.mp (by simpa [x.2])
    let y := hn.choose
    have hyx : H.Adj y x.1 := (H.adj_comm _ _).mp
      ((H.mem_neighborFinset x.1 y).mp hn.choose_spec)
    have hypos : 0 < H.degree y := by
      rw [← H.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨x.1, (H.mem_neighborFinset y x.1).mpr hyx⟩
    have hyle := hdeg y
    exact ⟨y, by omega⟩

theorem degreeOneMate_adj
    {X : Type*} [Fintype X] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x ≤ 1) (x : DegreeOneVertices H) :
    H.Adj x.1 (degreeOneMate H hdeg x).1 := by
  classical
  unfold degreeOneMate
  simp only
  exact (H.mem_neighborFinset x.1 _).mp (Finset.card_pos.mp (by simpa [x.2])).choose_spec

theorem degreeOneMate_involutive
    {X : Type*} [Fintype X] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x ≤ 1) :
    Function.Involutive (degreeOneMate H hdeg) := by
  intro x
  apply Subtype.ext
  have hback : H.Adj (degreeOneMate H hdeg x).1 x.1 :=
    (H.adj_comm _ _).mp (degreeOneMate_adj H hdeg x)
  have hchosen := degreeOneMate_adj H hdeg (degreeOneMate H hdeg x)
  have hone := (degreeOneMate H hdeg x).2
  rw [← H.card_neighborFinset_eq_degree] at hone
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hone
  have hchosenMem := (H.mem_neighborFinset _ _).mpr hchosen
  have hbackMem := (H.mem_neighborFinset _ _).mpr hback
  rw [hz] at hchosenMem hbackMem
  have hc : (degreeOneMate H hdeg (degreeOneMate H hdeg x)).1 = z := by
    simpa using hchosenMem
  have hb : x.1 = z := by simpa using hbackMem
  exact hc.trans hb.symm

theorem degreeOneMate_ne
    {X : Type*} [Fintype X] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x ≤ 1) (x : DegreeOneVertices H) :
    degreeOneMate H hdeg x ≠ x := by
  intro h
  have := degreeOneMate_adj H hdeg x
  rw [h] at this
  exact H.loopless.irrefl _ this

/-- The matched vertices in one second-layer branch. -/
abbrev OneHighMatchedBranchVertices
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s : {z : V // z ∈ G.neighborSet v}) :=
  DegreeOneVertices (G.induce (secondLayerBranch G v s))

/-- Intrinsic internal mate on a one-high second-layer branch. -/
noncomputable def oneHighInternalMate
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (s : {z : V // z ∈ G.neighborSet v}) :
    OneHighMatchedBranchVertices G v s → OneHighMatchedBranchVertices G v s :=
  degreeOneMate (G.induce (secondLayerBranch G v s))
    (degree_induce_secondLayerBranch_le_one G hfree v s)

/-- The unique missed far branch of an internally matched vertex. -/
noncomputable def oneHighMatchedMissLabel
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (s : {z : V // z ∈ G.neighborSet v})
    (x : OneHighMatchedBranchVertices G v s) :
    {z : V // z ∈ G.neighborSet v} :=
  oneHighMissingBranch G v rootMate s x.1.1

theorem oneHighMatchedMissLabel_mem
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (s : {z : V // z ∈ G.neighborSet v})
    (x : OneHighMatchedBranchVertices G v s) :
    oneHighMatchedMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj s x ∈
      oneHighFarMissBranches G v rootMate s x.1.1 := by
  have hxMatched :
      (G.neighborFinset x.1.1 ∩ secondLayerBranch G v s).card = 1 := by
    rw [← degree_induce_secondLayerBranch_eq_card_inter]
    exact x.2
  exact oneHighMissingBranch_mem_of_matched G hfree hv hexternal
    houterDegree rootMate hrootAdj s x.1.1 x.1.2 hxMatched

/-- Exact graph-side counting package for one branch: the abstract source
set counts precisely those internal matching edges whose unique miss labels
differ. -/
theorem oneHigh_branch_nonconstantMiss_counting_package
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (s : {z : V // z ∈ G.neighborSet v}) :
    let X := OneHighMatchedBranchVertices G v s
    let mate := oneHighInternalMate G hfree v s
    let label := oneHighMatchedMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj s
    Function.Involutive mate ∧
      (∀ x, mate x ≠ x) ∧
      (∀ x, label x ∈ oneHighFarMissBranches G v rootMate s x.1.1) ∧
      (∑ key ∈ exchangedMissPairKeys
          {z : V // z ∈ G.neighborSet v},
        exchangedMissPairMultiplicity mate label key) =
        (nonconstantMatchingEdgeSources mate label).card := by
  classical
  dsimp
  refine ⟨degreeOneMate_involutive _ _, degreeOneMate_ne _ _, ?_, ?_⟩
  · exact oneHighMatchedMissLabel_mem G hfree hv hexternal houterDegree
      rootMate hrootAdj s
  exact sum_exchangedMissPairMultiplicity_over_keys _ _

end

end Erdos85
