import Proofs.Erdos85OneHighOwnerPartitionDecoder

/-!
# Coherent geometry of the three odd-profile transversal witnesses

The odd one-high classification supplies a four-mate-pair transversal for
each of the three complementary partitions of `K₄`.  Choosing the three
owner edges simultaneously gives either a star or a triangle.  This packages
the coherence needed by downstream cross-target escape arguments; neither
alternative is discarded here.
-/

namespace Erdos85

/-- The owner-pair part of one prescribed transversal witness, retaining its
repeated key certificate. -/
def OneHighRefinementOwnerPairWitness
    (refinement : List (List OneHighLabelPair)) (code : Fin 3)
    (i j : Fin 8) : Prop :=
  i ≠ j ∧ j ≠ oneHighStandardMate i ∧
    (oneHighOwnerPartitionCode i j == code) = true ∧
    ∃ key : OneHighLabelPair,
      key.1 < key.2 ∧
      key.2 ≠ oneHighStandardMate key.1 ∧
      OneHighKeyFarFromSource key i ∧
      OneHighKeyFarFromSource key j ∧
      key ∈ refinement.getD i.val [] ∧
      key ∈ refinement.getD j.val []

/-- The coherent star-or-triangle geometry carried by three transversal
witnesses in one refinement. -/
def OneHighRefinementHasPartitionGeometry
    (refinement : List (List OneHighLabelPair)) : Prop :=
  ∃ i₀ j₀ i₁ j₁ i₂ j₂ : Fin 8,
    OneHighRefinementOwnerPairWitness refinement 0 i₀ j₀ ∧
    OneHighRefinementOwnerPairWitness refinement 1 i₁ j₁ ∧
    OneHighRefinementOwnerPairWitness refinement 2 i₂ j₂ ∧
    ((∃ z : Fin 4,
        z ∈ finFourEdge (oneHighRootPair i₀) (oneHighRootPair j₀) ∧
        z ∈ finFourEdge (oneHighRootPair i₁) (oneHighRootPair j₁) ∧
        z ∈ finFourEdge (oneHighRootPair i₂) (oneHighRootPair j₂)) ∨
      ((finFourEdge (oneHighRootPair i₀) (oneHighRootPair j₀) ∪
          finFourEdge (oneHighRootPair i₁) (oneHighRootPair j₁)) ∪
          finFourEdge (oneHighRootPair i₂) (oneHighRootPair j₂)).card = 3)

/-- Three prescribed transversal witnesses can be selected coherently so
that their owner mate-pair edges form either a star or a triangle. -/
theorem oneHighRefinement_transversalPartitions_star_or_triangle
    (refinement : List (List OneHighLabelPair))
    (hall : ∀ code : Fin 3,
      OneHighRefinementHasTransversalPartition refinement code) :
    OneHighRefinementHasPartitionGeometry refinement := by
  rcases hall 0 with ⟨i₀, j₀, h₀⟩
  rcases hall 1 with ⟨i₁, j₁, h₁⟩
  rcases hall 2 with ⟨i₂, j₂, h₂⟩
  unfold OneHighRefinementHasPartitionGeometry
  refine ⟨i₀, j₀, i₁, j₁, i₂, j₂, h₀, h₁, h₂, ?_⟩
  exact finFour_complementaryChoices_star_or_triangle
    (oneHighRootPair i₀) (oneHighRootPair j₀)
    (oneHighRootPair i₁) (oneHighRootPair j₁)
    (oneHighRootPair i₂) (oneHighRootPair j₂)
    (oneHighOwnerPartitionCode_zero_edge i₀ j₀ h₀.1 h₀.2.1 h₀.2.2.1)
    (oneHighOwnerPartitionCode_one_edge i₁ j₁ h₁.1 h₁.2.1 h₁.2.2.1)
    (oneHighOwnerPartitionCode_two_edge i₂ j₂ h₂.1 h₂.2.1 h₂.2.2.1)

/-- Graph-facing consumer: every odd-profile all-even graph refinement whose
relevant table is represented in the capacity inventory has coherent
star-or-triangle owner geometry. -/
theorem oneHigh_oddProfile_graphPairing_has_partitionGeometry
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
    OneHighRefinementHasPartitionGeometry
      (oneHighGraphPairingRefinement G hfree hv p) :=
  oneHighRefinement_transversalPartitions_star_or_triangle _
    (oneHigh_oddProfile_graphPairing_has_all_transversalPartitions
      G hfree hv p hprofile heven stored hstored hagree)

end Erdos85

#print axioms Erdos85.oneHighRefinement_transversalPartitions_star_or_triangle
#print axioms Erdos85.oneHigh_oddProfile_graphPairing_has_partitionGeometry
