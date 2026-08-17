import Proofs.Erdos85OneHighTurnTerminalCapstone
import Proofs.Erdos85OneHighTurnGraphInventoryBridge

/-! # Exact inventory for non-same-owner three-pair turns

The five source alternatives left by the ordered same-owner capstone are
fully visible in an exact pairing refinement: the two owner-row labels and
the three turn labels retain literal equality and standard-mate relations.
This file turns that observation into a finite checked-certificate socket.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Both endpoint orders represented by a stored canonical label pair. -/
def oneHighLabelPairOrientations (pair : OneHighLabelPair) :
    List OneHighLabelPair :=
  [pair, (pair.2, pair.1)]

theorem ordered_mem_oneHighLabelPairOrientations_canonical
    (a b : Fin 8) :
    (a, b) ∈ oneHighLabelPairOrientations
      (oneHighCanonicalLabelPair a b) := by
  rcases le_total a b with hab | hba
  · simp [oneHighLabelPairOrientations, oneHighCanonicalLabelPair,
      min_eq_left hab, max_eq_right hab]
  · simp [oneHighLabelPairOrientations, oneHighCanonicalLabelPair,
      min_eq_right hba, max_eq_left hba]

/-- An exact refinement contains a three-pair odd turn whose two source rows
satisfy one of the five decoded non-same-owner relations.  The evaluator only
visits pairs actually stored in the two rows and their two orientations. -/
def oneHighRefinementHasNonSameOwnerOddTurn
    (refinement : List (List OneHighLabelPair)) : Bool :=
  let labels := List.ofFn (fun i : Fin 8 ↦ i)
  labels.any fun sourceAB =>
  labels.any fun sourceBC =>
  (refinement.getD sourceAB.val []).any fun pairAB =>
  (refinement.getD sourceBC.val []).any fun pairBC =>
  (oneHighLabelPairOrientations pairAB).any fun orientedAB =>
  (oneHighLabelPairOrientations pairBC).any fun orientedBC =>
    decide (
      orientedAB.2 = orientedBC.1 ∧
      let a := orientedAB.1
      let b := orientedAB.2
      let c := orientedBC.2
      oneHighRootPair a ≠ oneHighRootPair b ∧
      oneHighRootPair b ≠ oneHighRootPair c ∧
      oneHighRootPair a ≠ oneHighRootPair c ∧
      oneHighMultiplicityOdd refinement a b = true ∧
      oneHighMultiplicityOdd refinement b c = true ∧
      (sourceAB = oneHighStandardMate sourceBC ∨
       sourceAB = c ∨ sourceAB = oneHighStandardMate c ∨
       sourceBC = a ∨ sourceBC = oneHighStandardMate a))

def oneHighTableHasNonSameOwnerOddTurn
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  (oneHighPairingRefinements profile (oneHighTableRestrict table)).any
    oneHighRefinementHasNonSameOwnerOddTurn

/-- Capacity rows admitting an exact non-same-owner odd-turn refinement. -/
def oneHighNonSameOwnerOddTurnInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter
    (oneHighTableHasNonSameOwnerOddTurn profile.val)

theorem mem_oneHighNonSameOwnerOddTurnInventoryTables_of_refinement
    {profile : Fin 5} {table : OneHighMissTable}
    (hcapacity : table ∈ oneHighCapacityInventoryTables profile)
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈
      oneHighPairingRefinements profile.val (oneHighTableRestrict table))
    (hturn : oneHighRefinementHasNonSameOwnerOddTurn refinement = true) :
    table ∈ oneHighNonSameOwnerOddTurnInventoryTables profile := by
  rw [oneHighNonSameOwnerOddTurnInventoryTables, List.mem_filter]
  refine ⟨hcapacity, ?_⟩
  rw [oneHighTableHasNonSameOwnerOddTurn, List.any_eq_true]
  exact ⟨refinement, hrefinement, hturn⟩

/-- Every pinned turn in one of the five decoded residual source sectors has
the executable signature in the actual graph-induced refinement. -/
theorem OneHighPinnedThreePairTurn.graphPairingRefinement_hasNonSameOwnerOddTurn
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p)
    (hsector : T.qAB.sourceEdge.1 = p.mate T.qBC.sourceEdge.1 ∨
       T.qAB.sourceEdge.1 = T.c ∨
       T.qAB.sourceEdge.1 = p.mate T.c ∨
       T.qBC.sourceEdge.1 = T.a ∨
       T.qBC.sourceEdge.1 = p.mate T.a) :
    oneHighRefinementHasNonSameOwnerOddTurn
      (oneHighGraphPairingRefinement G hfree hv p) = true := by
  rw [oneHighRefinementHasNonSameOwnerOddTurn]
  simp only [List.any_eq_true]
  let sourceAB := p.branchLabel T.qAB.sourceEdge.1
  let sourceBC := p.branchLabel T.qBC.sourceEdge.1
  let pairAB := oneHighCanonicalLabelPair
    (p.branchLabel T.a) (p.branchLabel T.b)
  let pairBC := oneHighCanonicalLabelPair
    (p.branchLabel T.b) (p.branchLabel T.c)
  let orientedAB : OneHighLabelPair :=
    (p.branchLabel T.a, p.branchLabel T.b)
  let orientedBC : OneHighLabelPair :=
    (p.branchLabel T.b, p.branchLabel T.c)
  refine ⟨sourceAB, ?_, sourceBC, ?_, pairAB, ?_, pairBC, ?_,
    orientedAB, ?_, orientedBC, ?_, ?_⟩
  · rw [List.mem_ofFn]; exact ⟨sourceAB, rfl⟩
  · rw [List.mem_ofFn]; exact ⟨sourceBC, rfl⟩
  · change oneHighCanonicalLabelPair (p.branchLabel T.a)
      (p.branchLabel T.b) ∈
        (List.ofFn fun s : Fin 8 ↦
          oneHighGraphSourcePairing G hfree hv p s).getD sourceAB.val []
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp [sourceAB]),
      Option.getD_some, List.getElem_ofFn]
    exact T.qAB.canonicalPair_mem_graphSourcePairing G hfree hv p
  · change oneHighCanonicalLabelPair (p.branchLabel T.b)
      (p.branchLabel T.c) ∈
        (List.ofFn fun s : Fin 8 ↦
          oneHighGraphSourcePairing G hfree hv p s).getD sourceBC.val []
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp [sourceBC]),
      Option.getD_some, List.getElem_ofFn]
    exact T.qBC.canonicalPair_mem_graphSourcePairing G hfree hv p
  · exact ordered_mem_oneHighLabelPairOrientations_canonical _ _
  · exact ordered_mem_oneHighLabelPairOrientations_canonical _ _
  rw [decide_eq_true_eq]
  refine ⟨rfl, T.ab_pair_ne, T.bc_pair_ne, T.ac_pair_ne,
    (oneHighMultiplicityOdd_eq_true_iff _ _ _).2
      (T.graphPairingMultiplicity_ab_odd G hfree hv p),
    (oneHighMultiplicityOdd_eq_true_iff _ _ _).2
      (T.graphPairingMultiplicity_bc_odd G hfree hv p), ?_⟩
  · rcases hsector with hmate | hc | hmc | ha | hma
    · left
      dsimp [sourceAB, sourceBC]
      calc
        p.branchLabel T.qAB.sourceEdge.1 =
            p.branchLabel (p.mate T.qBC.sourceEdge.1) :=
          congrArg p.branchLabel hmate
        _ = oneHighStandardMate (p.branchLabel T.qBC.sourceEdge.1) :=
          p.branch_mate _
    · exact Or.inr (Or.inl (by
        dsimp [sourceAB]; exact congrArg p.branchLabel hc))
    · exact Or.inr (Or.inr (Or.inl (by
        dsimp [sourceAB]
        calc
          p.branchLabel T.qAB.sourceEdge.1 = p.branchLabel (p.mate T.c) :=
            congrArg p.branchLabel hmc
          _ = oneHighStandardMate (p.branchLabel T.c) := p.branch_mate _)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (by dsimp [sourceBC]; exact congrArg p.branchLabel ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by
        dsimp [sourceBC]
        calc
          p.branchLabel T.qBC.sourceEdge.1 = p.branchLabel (p.mate T.a) :=
            congrArg p.branchLabel hma
          _ = oneHighStandardMate (p.branchLabel T.a) := p.branch_mate _))))

/-- Graph-to-inventory socket for all five non-same-owner source sectors. -/
theorem OneHighPinnedThreePairTurn.mem_nonSameOwnerOddTurnInventory
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p)
    (hsector : T.qAB.sourceEdge.1 = p.mate T.qBC.sourceEdge.1 ∨
       T.qAB.sourceEdge.1 = T.c ∨
       T.qAB.sourceEdge.1 = p.mate T.c ∨
       T.qBC.sourceEdge.1 = T.a ∨
       T.qBC.sourceEdge.1 = p.mate T.a)
    (table : OneHighMissTable)
    (hcapacity : table ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v
            p.branchLabel p.leafLabel)) p.profile) table) :
    table ∈ oneHighNonSameOwnerOddTurnInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ := by
  have hrefinement :=
    oneHighGraphPairingRefinement_mem_restrict_graphTable G hfree hv p
  rw [oneHighTableRestrict_eq_of_relevantAgree hagree] at hrefinement
  exact mem_oneHighNonSameOwnerOddTurnInventoryTables_of_refinement
    hcapacity hrefinement
      (T.graphPairingRefinement_hasNonSameOwnerOddTurn
        G hfree hv p hsector)

/-- A checked row in the non-same-owner inventory closes the actual graph
presentation after transporting the certificate through relevant agreement. -/
theorem false_of_nonSameOwnerPinnedThreePairTurn_checked
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {v : Fin 49} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p)
    (hsector : T.qAB.sourceEdge.1 = p.mate T.qBC.sourceEdge.1 ∨
       T.qAB.sourceEdge.1 = T.c ∨
       T.qAB.sourceEdge.1 = p.mate T.c ∨
       T.qBC.sourceEdge.1 = T.a ∨
       T.qBC.sourceEdge.1 = p.mate T.a)
    (table : OneHighMissTable)
    (hcapacity : table ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v
            p.branchLabel p.leafLabel)) p.profile) table)
    (hchecked : ∀ stored,
      stored ∈ oneHighNonSameOwnerOddTurnInventoryTables
        ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ →
      OneHighFamilyV2CheckedUnsat p.profile stored) : False := by
  have hmem := T.mem_nonSameOwnerOddTurnInventory
    G hfree hv p hsector table hcapacity hagree
  have hcert : OneHighFamilyV2CheckedUnsat p.profile
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v
            p.branchLabel p.leafLabel)) p.profile) :=
    (hchecked table hmem).transport hagree.symm
  exact false_of_rawOneHigh_v2Checked
    G hfree hmin (Fintype.card_fin 49) hv p.unique_high p.external_empty
      p.outer_degree p.mate p.mate_involutive p.mate_adj p.branchLabel
      p.branch_mate p.leafLabel p.profile p.constraints hcert

/-- Complete one-high exclusion from the already-independent structural
terminals and two finite, exact turn inventories.  No residual source-geometry
hypothesis remains in this interface. -/
theorem orderFortyNineStratumExcluded_one_of_finiteTurnInventories
    (hall : OneHighAllEvenSectorExcluded)
    (hhexagon : OneHighMateMissHexagonSectorExcluded)
    (hcross : OneHighCrossBlockSectorExcluded)
    (hcheckedSame : ∀ (profile : Fin 5) table,
      table ∈ oneHighSaturatedOddTurnResidualInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (hcheckedOther : ∀ (profile : Fin 5) table,
      table ∈ oneHighNonSameOwnerOddTurnInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table) :
    OrderFortyNineStratumExcluded 1 := by
  intro G _ _ _ hfree hmin hHigh
  obtain ⟨v, hv, p, table, hcapacity, hagree⟩ :=
    oneHighRawV2OrbitCover_capacityInventory G inferInstance inferInstance
      inferInstance hfree hmin hHigh
  rcases orderFortyNine_oneHigh_structural_sector_capstone
      G hfree hmin (Fintype.card_fin 49) hv p with
    heven | hmate | hturn | hcrossBlock
  · exact hall G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p heven
  · exact hhexagon G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p hmate
  · obtain ⟨T⟩ := nonempty_oneHighPinnedThreePairTurn_of_multiplicityTurn
      G hfree hv p hturn
    rcases T.fully_decoded_source_sector G hfree hv p with
      hsame | hmateOwner | hc | hmc | ha | hma
    · exact false_of_sameOwnerPinnedThreePairTurn_of_structuralTerminals
        hhexagon hcross G hfree hmin hHigh hv p T hsame table
          hcapacity hagree (fun stored hmem =>
            hcheckedSame ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩
              stored hmem)
    · exact false_of_nonSameOwnerPinnedThreePairTurn_checked
        G hfree hmin hv p T (Or.inl hmateOwner) table hcapacity hagree
          (fun stored hmem => hcheckedOther
            ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ stored hmem)
    · exact false_of_nonSameOwnerPinnedThreePairTurn_checked
        G hfree hmin hv p T (Or.inr (Or.inl hc)) table hcapacity hagree
          (fun stored hmem => hcheckedOther
            ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ stored hmem)
    · exact false_of_nonSameOwnerPinnedThreePairTurn_checked
        G hfree hmin hv p T (Or.inr (Or.inr (Or.inl hmc))) table
          hcapacity hagree (fun stored hmem => hcheckedOther
            ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ stored hmem)
    · exact false_of_nonSameOwnerPinnedThreePairTurn_checked
        G hfree hmin hv p T (Or.inr (Or.inr (Or.inr (Or.inl ha)))) table
          hcapacity hagree (fun stored hmem => hcheckedOther
            ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ stored hmem)
    · exact false_of_nonSameOwnerPinnedThreePairTurn_checked
        G hfree hmin hv p T (Or.inr (Or.inr (Or.inr (Or.inr hma)))) table
          hcapacity hagree (fun stored hmem => hcheckedOther
            ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ stored hmem)
  · exact hcross G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p hcrossBlock

end

end Erdos85
