import Proofs.Erdos85OneHighOddProfileRepeatedOwnerCoherentLocalEdges
import Proofs.Erdos85OneHighOddProfilePartitionEscape

/-! # Orient repeated-owner witnesses toward one shared escape branch -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Package the target-escape conclusion so two partition witnesses can be
compared without losing the concrete local-edge witnesses that produced it. -/
def OneHighPartitionTargetEscape
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} {code : Fin 3}
    (q : OneHighPartitionLocalEdgeWitness G hfree hv p code) : Prop :=
  ∃ x : OneHighMatchedBranchVertices G v q.s,
    ∃ y : OneHighMatchedBranchVertices G v q.t,
      ∃ a b : V,
        x ∈ matchingEdgeSources (oneHighInternalMate G hfree v q.s) ∧
        y ∈ matchingEdgeSources (oneHighInternalMate G hfree v q.t) ∧
        a ∈ secondLayerBranch G v q.t ∧
        b ∈ secondLayerBranch G v q.t ∧
        G.Adj x.1.1 a ∧
        G.Adj (oneHighInternalMate G hfree v q.s x).1.1 b ∧
        a ≠ b ∧ ¬ G.Adj a b ∧
        ((a ≠ y.1.1 ∧
            a ≠ (oneHighInternalMate G hfree v q.t y).1.1) ∨
          (b ≠ y.1.1 ∧
            b ≠ (oneHighInternalMate G hfree v q.t y).1.1))

/-- Put either endpoint of a local-edge witness into its target slot. -/
theorem OneHighPartitionLocalEdgeWitness.exists_orient_target
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} {code : Fin 3}
    (q : OneHighPartitionLocalEdgeWitness G hfree hv p code)
    (z : {x : V // x ∈ G.neighborSet v})
    (hz : z ∈ ({q.s, q.t} : Finset _)) :
    ∃ q' : OneHighPartitionLocalEdgeWitness G hfree hv p code,
      q'.t = z := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with hz | hz
  · obtain ⟨q', -, htarget⟩ := q.exists_swap
    exact ⟨q', htarget.trans hz.symm⟩
  · exact ⟨q, hz.symm⟩

/-- Two concrete local-edge witnesses with a common endpoint can be oriented
toward that same graph branch, and each then forces its escape there. -/
theorem oneHigh_exists_oriented_targetEscapes
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} {c d : Fin 3}
    (q : OneHighPartitionLocalEdgeWitness G hfree hv p c)
    (r : OneHighPartitionLocalEdgeWitness G hfree hv p d)
    (z : {x : V // x ∈ G.neighborSet v})
    (hzq : z ∈ ({q.s, q.t} : Finset _))
    (hzr : z ∈ ({r.s, r.t} : Finset _)) :
    ∃ q' : OneHighPartitionLocalEdgeWitness G hfree hv p c,
      ∃ r' : OneHighPartitionLocalEdgeWitness G hfree hv p d,
        q'.t = z ∧ r'.t = z ∧
          OneHighPartitionTargetEscape q' ∧
          OneHighPartitionTargetEscape r' := by
  obtain ⟨q', hq'⟩ := q.exists_orient_target z hzq
  obtain ⟨r', hr'⟩ := r.exists_orient_target z hzr
  exact ⟨q', r', hq', hr', q'.exists_targetEscape,
    r'.exists_targetEscape⟩

/-- The odd all-even graph case contains two different partition codes whose
forced target escapes occur in one exact shared graph branch. -/
theorem oneHigh_oddProfile_exists_repeatedOwner_orientedTargetEscapes
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hprofile : p.profile = 1 ∨ p.profile = 3)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key))
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored) :
    ∃ z : {x : V // x ∈ G.neighborSet v},
      (∃ q₀ : OneHighPartitionLocalEdgeWitness G hfree hv p 0,
        ∃ q₁ : OneHighPartitionLocalEdgeWitness G hfree hv p 1,
          q₀.t = z ∧ q₁.t = z ∧
            OneHighPartitionTargetEscape q₀ ∧
            OneHighPartitionTargetEscape q₁) ∨
      (∃ q₀ : OneHighPartitionLocalEdgeWitness G hfree hv p 0,
        ∃ q₂ : OneHighPartitionLocalEdgeWitness G hfree hv p 2,
          q₀.t = z ∧ q₂.t = z ∧
            OneHighPartitionTargetEscape q₀ ∧
            OneHighPartitionTargetEscape q₂) ∨
      (∃ q₁ : OneHighPartitionLocalEdgeWitness G hfree hv p 1,
        ∃ q₂ : OneHighPartitionLocalEdgeWitness G hfree hv p 2,
          q₁.t = z ∧ q₂.t = z ∧
            OneHighPartitionTargetEscape q₁ ∧
            OneHighPartitionTargetEscape q₂) := by
  obtain ⟨q₀, q₁, q₂, z, hshared⟩ :=
    oneHigh_oddProfile_exists_partitionLocalEdges_with_repeatedOwner
      G hfree hv p hprofile heven stored hstored hagree
  refine ⟨z, ?_⟩
  rcases hshared with h01 | h02 | h12
  · left
    exact oneHigh_exists_oriented_targetEscapes q₀ q₁ z h01.1 h01.2
  · right; left
    exact oneHigh_exists_oriented_targetEscapes q₀ q₂ z h02.1 h02.2
  · right; right
    exact oneHigh_exists_oriented_targetEscapes q₁ q₂ z h12.1 h12.2

end

end Erdos85

#print axioms Erdos85.OneHighPartitionLocalEdgeWitness.exists_orient_target
#print axioms Erdos85.oneHigh_exists_oriented_targetEscapes
#print axioms Erdos85.oneHigh_oddProfile_exists_repeatedOwner_orientedTargetEscapes
