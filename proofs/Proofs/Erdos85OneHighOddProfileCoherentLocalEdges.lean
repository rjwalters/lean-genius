import Proofs.Erdos85OneHighOddProfilePartitionGeometry
import Proofs.Erdos85OneHighOddProfilePartitionLocalEdges
import Proofs.Erdos85OneHighOwnerPartitionDecoder

/-!
# Coherent concrete local edges in odd one-high profiles

This combines the code-preserving inversion of each transversal with the
star-or-triangle geometry of the three owner pairs.  The resulting package
retains all six internal matching edges and all three repeated keys, so the
next cross-target argument can count detours across the witnesses jointly.
-/

namespace Erdos85

/-- A concrete pair of internal branch edges carrying one repeated key for a
prescribed complementary-partition code. -/
structure OneHighPartitionLocalEdgeWitness
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (code : Fin 3) where
  s : {z : V // z ∈ G.neighborSet v}
  t : {z : V // z ∈ G.neighborSet v}
  source_ne : s ≠ t
  target_ne_mate : t ≠ p.mate s
  code_eq :
    (oneHighOwnerPartitionCode (p.branchLabel s) (p.branchLabel t) ==
      code) = true
  edge_data : ∃ key : OneHighLabelPair,
    key.1 < key.2 ∧
    key.2 ≠ oneHighStandardMate key.1 ∧
    OneHighKeyFarFromSource key (p.branchLabel s) ∧
    OneHighKeyFarFromSource key (p.branchLabel t) ∧
    ∃ x ∈ matchingEdgeSources (oneHighInternalMate G hfree v s),
      (min (p.branchLabel (oneHighMatchedMissLabel G hfree hv
          p.external_empty p.outer_degree p.mate p.mate_adj s x))
          (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj s
              (oneHighInternalMate G hfree v s x))),
        max (p.branchLabel (oneHighMatchedMissLabel G hfree hv
          p.external_empty p.outer_degree p.mate p.mate_adj s x))
          (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj s
              (oneHighInternalMate G hfree v s x)))) = key ∧
    ∃ y ∈ matchingEdgeSources (oneHighInternalMate G hfree v t),
      (min (p.branchLabel (oneHighMatchedMissLabel G hfree hv
          p.external_empty p.outer_degree p.mate p.mate_adj t y))
          (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj t
              (oneHighInternalMate G hfree v t y))),
        max (p.branchLabel (oneHighMatchedMissLabel G hfree hv
          p.external_empty p.outer_degree p.mate p.mate_adj t y))
          (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj t
              (oneHighInternalMate G hfree v t y)))) = key

/-- Package the existing code-preserving graph inversion as a reusable
dependent witness. -/
theorem oneHigh_oddProfile_nonempty_partitionLocalEdgeWitness
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
        p.profile) stored)
    (code : Fin 3) :
    Nonempty (OneHighPartitionLocalEdgeWitness G hfree hv p code) := by
  obtain ⟨s, t, hst, htMate, hcode, hdata⟩ :=
    oneHigh_oddProfile_exists_partitionLocalEdges
      G hfree hv p hprofile heven stored hstored hagree code
  exact ⟨⟨s, t, hst, htMate, hcode, hdata⟩⟩

/-- Select the three concrete repeated-key edge pairs simultaneously.  Their
owner root-pair edges have the exact star-or-triangle coherence split. -/
theorem oneHigh_oddProfile_exists_coherentPartitionLocalEdges
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
    ∃ q₀ : OneHighPartitionLocalEdgeWitness G hfree hv p 0,
      ∃ q₁ : OneHighPartitionLocalEdgeWitness G hfree hv p 1,
        ∃ q₂ : OneHighPartitionLocalEdgeWitness G hfree hv p 2,
          (∃ z : Fin 4,
              z ∈ finFourEdge (oneHighRootPair (p.branchLabel q₀.s))
                (oneHighRootPair (p.branchLabel q₀.t)) ∧
              z ∈ finFourEdge (oneHighRootPair (p.branchLabel q₁.s))
                (oneHighRootPair (p.branchLabel q₁.t)) ∧
              z ∈ finFourEdge (oneHighRootPair (p.branchLabel q₂.s))
                (oneHighRootPair (p.branchLabel q₂.t))) ∨
            ((finFourEdge (oneHighRootPair (p.branchLabel q₀.s))
                (oneHighRootPair (p.branchLabel q₀.t)) ∪
              finFourEdge (oneHighRootPair (p.branchLabel q₁.s))
                (oneHighRootPair (p.branchLabel q₁.t))) ∪
              finFourEdge (oneHighRootPair (p.branchLabel q₂.s))
                (oneHighRootPair (p.branchLabel q₂.t))).card = 3 := by
  obtain ⟨q₀⟩ := oneHigh_oddProfile_nonempty_partitionLocalEdgeWitness
    G hfree hv p hprofile heven stored hstored hagree 0
  obtain ⟨q₁⟩ := oneHigh_oddProfile_nonempty_partitionLocalEdgeWitness
    G hfree hv p hprofile heven stored hstored hagree 1
  obtain ⟨q₂⟩ := oneHigh_oddProfile_nonempty_partitionLocalEdgeWitness
    G hfree hv p hprofile heven stored hstored hagree 2
  refine ⟨q₀, q₁, q₂, ?_⟩
  exact oneHigh_threeOwnerPartitions_star_or_triangle
    (p.branchLabel q₀.s) (p.branchLabel q₀.t)
    (p.branchLabel q₁.s) (p.branchLabel q₁.t)
    (p.branchLabel q₂.s) (p.branchLabel q₂.t)
    (fun h => q₀.source_ne (p.branchLabel.injective h))
    (by
      intro h
      apply q₀.target_ne_mate
      exact p.branchLabel.injective (by simpa [p.branch_mate] using h))
    q₀.code_eq
    (fun h => q₁.source_ne (p.branchLabel.injective h))
    (by
      intro h
      apply q₁.target_ne_mate
      exact p.branchLabel.injective (by simpa [p.branch_mate] using h))
    q₁.code_eq
    (fun h => q₂.source_ne (p.branchLabel.injective h))
    (by
      intro h
      apply q₂.target_ne_mate
      exact p.branchLabel.injective (by simpa [p.branch_mate] using h))
    q₂.code_eq

end Erdos85

#print axioms Erdos85.oneHigh_oddProfile_nonempty_partitionLocalEdgeWitness
#print axioms Erdos85.oneHigh_oddProfile_exists_coherentPartitionLocalEdges
