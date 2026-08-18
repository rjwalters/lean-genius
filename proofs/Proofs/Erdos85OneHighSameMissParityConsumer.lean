import Proofs.Erdos85OneHighSameMissCountingBridge
import Proofs.Erdos85OneHighSameMissParity

/-! # Feeding the global counting predicate into same-miss parity -/

namespace Erdos85

noncomputable section

/-- The sigma-level same-miss predicate implies the arbitrary internal-edge
form consumed by the parity theorem. -/
theorem internalEdge_sameMiss_of_globalSameMiss
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hsame : OneHighGlobalSameMiss G hfree v rootMate) :
    ∀ (s : {z : V // z ∈ G.neighborSet v}) {x y : V},
      x ∈ secondLayerBranch G v s →
      y ∈ secondLayerBranch G v s → G.Adj x y →
      ∀ u ∈ ((Finset.univ.erase s).erase (rootMate s)),
      ((G.neighborFinset x ∩ secondLayerBranch G v u).card = 0 ↔
       (G.neighborFinset y ∩ secondLayerBranch G v u).card = 0) := by
  intro s x y hxs hys hxy u hu
  let B := secondLayerBranch G v s
  let H := G.induce B
  let xb : B := ⟨x, hxs⟩
  let yb : B := ⟨y, hys⟩
  have hdeg : ∀ z : B, H.degree z ≤ 1 :=
    degree_induce_secondLayerBranch_le_one G hfree v s
  have hxPos : 0 < H.degree xb := by
    rw [← H.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨yb, (H.mem_neighborFinset xb yb).mpr hxy⟩
  have hxOne : H.degree xb = 1 := by
    have := hdeg xb
    omega
  let xm : DegreeOneVertices H := ⟨xb, hxOne⟩
  have hmateAdj : H.Adj xm.1 (degreeOneMate H hdeg xm).1 :=
    degreeOneMate_adj H hdeg xm
  have hneighborCard : (H.neighborFinset xm.1).card = 1 := by
    rw [H.card_neighborFinset_eq_degree]
    exact xm.2
  have hmateEq : (degreeOneMate H hdeg xm).1 = yb := by
    have hmMem := (H.mem_neighborFinset xm.1 _).mpr hmateAdj
    have hyMem := (H.mem_neighborFinset xm.1 yb).mpr hxy
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hneighborCard
    rw [hz] at hmMem hyMem
    have hmz : (degreeOneMate H hdeg xm).1 = z := by simpa using hmMem
    have hyz : yb = z := by simpa using hyMem
    exact hmz.trans hyz.symm
  have h := hsame (⟨s, xm⟩ : OneHighAllMatchedVertices G v) u hu
  change
    ((G.neighborFinset x ∩ secondLayerBranch G v u).card = 0 ↔
      (G.neighborFinset (degreeOneMate H hdeg xm).1.1 ∩
        secondLayerBranch G v u).card = 0) at h
  rw [hmateEq] at h
  exact h

/-- Vanishing of the global nonconstant-edge source set makes every directed
far-branch miss count even. -/
theorem even_highBranchMissCount_of_nonconstantSources_eq_empty
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (hempty : nonconstantMatchingEdgeSources
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj) = ∅) :
    ∀ s u, u ∈ ((Finset.univ.erase s).erase (rootMate s)) →
      Even (highBranchMissCount G v s u) := by
  have hglobal : OneHighGlobalSameMiss G hfree v rootMate :=
    (oneHigh_nonconstantSources_eq_empty_iff_globalSameMiss
      G hfree hv hexternal houterDegree rootMate hrootAdj).mp hempty
  apply even_highBranchMissCount_of_sameMiss G hfree (d := 7) (by omega) hexternal
    rootMate hrootAdj houterDegree
  exact internalEdge_sameMiss_of_globalSameMiss G hfree v rootMate hglobal

end

end Erdos85
