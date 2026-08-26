import Proofs.Erdos85OneHighGraphCanonicalSlotCoverage
import Proofs.Erdos85OneHighAllEvenCapacityTerminal
import Proofs.Erdos85OneHighMultiplicitySectorSupport
import Proofs.Erdos85OneHighOddProfileSlotVariantInventory
import Proofs.Erdos85OneHighRefinementPinnedExclusion

/-!
# Refinement-pin sockets for the odd-support one-high sectors

The existing 122-certificate bank deliberately covers only all-even
refinements.  The three-pair-turn and cross-block sectors use the same exact
pinned CNF, but need their own finite refinement inventories and certificate
banks.  This file defines the common capacity-refinement universe and proves
the graph-facing terminal once a Boolean sector predicate and its checked bank
are supplied.
-/

namespace Erdos85

noncomputable section

/-- Every pairing refinement attached to a capacity-compatible orbit row,
before filtering by parity sector or expanding canonical edge-slot order. -/
def oneHighCapacityInventoryRefinements (profile : Fin 5) :
    List (List (List OneHighLabelPair)) :=
  (oneHighCapacityInventoryTables profile).flatMap fun table =>
    oneHighPairingRefinements profile.val
      (oneHighPairingTableRestrict table)

/-- Canonical-slot variants in a selected executable parity sector. -/
def oneHighCapacitySectorSlotVariants
    (accept : List (List OneHighLabelPair) → Bool) (profile : Fin 5) :
    List (List (List OneHighLabelPair)) :=
  ((oneHighCapacityInventoryRefinements profile).filter accept).flatMap
    oneHighRefinementSlotVariants

/-- Checked refinement-pin evidence for every capacity refinement selected by
`accept`, with every graph-compatible canonical edge-slot ordering included. -/
def OneHighCapacitySectorRefinementPinBank
    (accept : List (List OneHighLabelPair) → Bool) : Prop :=
  ∀ profile : Fin 5, ∀ refinement,
    refinement ∈ oneHighCapacitySectorSlotVariants accept profile →
      OneHighRefinementCheckedUnsat profile.val refinement

/-- The exact finite target for the three-pair-turn sector. -/
def oneHighThreePairTurnCapacitySlotVariants (profile : Fin 5) :=
  oneHighCapacitySectorSlotVariants
    oneHighRefinementHasOddThreePairTurn profile

/-- The exact finite target for the complete cross-block sector. -/
def oneHighCrossBlockCapacitySlotVariants (profile : Fin 5) :=
  oneHighCapacitySectorSlotVariants
    oneHighRefinementHasOddCrossBlock profile

def OneHighThreePairTurnRefinementPinBank : Prop :=
  OneHighCapacitySectorRefinementPinBank
    oneHighRefinementHasOddThreePairTurn

def OneHighCrossBlockRefinementPinBank : Prop :=
  OneHighCapacitySectorRefinementPinBank
    oneHighRefinementHasOddCrossBlock

/-- The graph's sorted pairing refinement belongs to the unfiltered capacity
refinement universe of any stored orbit representative agreeing on the
relevant miss-table coordinates. -/
theorem oneHighGraphPairingRefinement_mem_capacityInventoryRefinements
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored) :
    oneHighGraphPairingRefinement G hfree hv p ∈
      oneHighCapacityInventoryRefinements
        ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ := by
  let table := oneHighGraphRelevantMissTable
    (oneHighRelabeledLeafGraph G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)) p.profile
  have htableRestrict : oneHighPairingTableRestrict table = table :=
    oneHighTableRestrict_graphRelevantMissTable _ _
  have hrel : OneHighTableRelevantAgree table stored :=
    oneHighGraphRelevantMissTable_relevantAgree_of_graphTable _ _ hagree
  have hrestrictEq : oneHighPairingTableRestrict table =
      oneHighPairingTableRestrict stored :=
    oneHighPairingTableRestrict_eq_of_relevantAgree hrel
  have hrefinement : oneHighGraphPairingRefinement G hfree hv p ∈
      oneHighPairingRefinements p.profile table :=
    oneHighGraphPairingRefinement_mem G hfree hv p
  have hrefinementStored : oneHighGraphPairingRefinement G hfree hv p ∈
      oneHighPairingRefinements p.profile
        (oneHighPairingTableRestrict stored) := by
    rw [htableRestrict] at hrestrictEq
    rwa [hrestrictEq] at hrefinement
  rw [oneHighCapacityInventoryRefinements, List.mem_flatMap]
  exact ⟨stored, hstored, hrefinementStored⟩

/-- Generic graph-facing certificate socket for an executable odd-support
sector.  This is the common terminal used by the turn and cross-block banks. -/
theorem false_of_oneHigh_capacitySector_refinementPinBank
    (accept : List (List OneHighLabelPair) → Bool)
    (hbank : OneHighCapacitySectorRefinementPinBank accept)
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored)
    (haccept : accept (oneHighGraphPairingRefinement G hfree hv p) = true) :
    False := by
  let profile : Fin 5 :=
    ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩
  have hsorted : oneHighGraphPairingRefinement G hfree hv p ∈
      (oneHighCapacityInventoryRefinements profile).filter accept :=
    List.mem_filter.mpr ⟨
      oneHighGraphPairingRefinement_mem_capacityInventoryRefinements
        G hfree hv p stored hstored hagree,
      haccept⟩
  have hvariant : oneHighGraphCanonicalSlotRefinement G hfree p ∈
      oneHighCapacitySectorSlotVariants accept profile := by
    rw [oneHighCapacitySectorSlotVariants, List.mem_flatMap]
    exact ⟨oneHighGraphPairingRefinement G hfree hv p, hsorted,
      oneHighRefinementSlotVariants_mem
        (oneHighGraphCanonicalSlotRefinement_slotCompatible G hfree hv p)⟩
  have hchecked : OneHighRefinementCheckedUnsat p.profile
      (oneHighGraphCanonicalSlotRefinement G hfree p) := by
    simpa [profile] using hbank profile _ hvariant
  exact false_of_oneHighRefinementCheckedUnsat hchecked
    (oneHighRelabeledLeafGraph G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
    p.constraints
    (oneHighGraphCanonicalSlotRefinement_pinSemantics G hfree hv p)

private theorem oneHighGraphPairingRefinement_multiplicity_odd_iff
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) {a b : Fin 8}
    (hab : a ≠ b) :
    Odd (oneHighPairingRefinementMultiplicity
      (oneHighGraphPairingRefinement G hfree hv p)
      (oneHighCanonicalLabelPair a b)) ↔
    Odd (exchangedMissPairMultiplicity
      (oneHighGlobalInternalMate G hfree v)
      (fun x => p.branchLabel
        (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj x))
      (oneHighCanonicalLabelPair a b)) := by
  rw [oneHighGraphPairingRefinementMultiplicity_eq_global]
  exact min_lt_max.mpr hab

/-- A checked turn-sector refinement bank excludes a graph carrying the
three-root-pair odd turn, once its capacity-orbit representative is supplied. -/
theorem false_of_oneHigh_threePairTurn_refinementPinBank
    (hbank : OneHighThreePairTurnRefinementPinBank)
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored)
    (hturn : OneHighOddSupportThreePairTurnProp
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)))) : False := by
  apply false_of_oneHigh_capacitySector_refinementPinBank
    oneHighRefinementHasOddThreePairTurn hbank
    G hfree hv p stored hstored hagree
  apply (oneHighRefinementHasOddThreePairTurn_eq_true_iff _).2
  obtain ⟨a, b, c, habRoot, hbcRoot, hacRoot, habOdd, hbcOdd⟩ := hturn
  have hab : a ≠ b := habOdd.1
  have hbc : b ≠ c := hbcOdd.1
  refine ⟨a, b, c, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact habRoot ((oneHighLabelPairColor_eq_iff_rootPair_eq a b).1 h)
  · intro h
    exact hbcRoot ((oneHighLabelPairColor_eq_iff_rootPair_eq b c).1 h)
  · intro h
    exact hacRoot ((oneHighLabelPairColor_eq_iff_rootPair_eq a c).1 h)
  · exact (oneHighGraphPairingRefinement_multiplicity_odd_iff
      G hfree hv p hab).2 habOdd.2
  · exact (oneHighGraphPairingRefinement_multiplicity_odd_iff
      G hfree hv p hbc).2 hbcOdd.2

/-- A checked cross-block refinement bank excludes a graph carrying the
complete odd `2 × 2` block between two standard root pairs. -/
theorem false_of_oneHigh_crossBlock_refinementPinBank
    (hbank : OneHighCrossBlockRefinementPinBank)
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored)
    (hcross : OneHighOddSupportCrossBlockProp
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)))) : False := by
  apply false_of_oneHigh_capacitySector_refinementPinBank
    oneHighRefinementHasOddCrossBlock hbank
    G hfree hv p stored hstored hagree
  apply (oneHighRefinementHasOddCrossBlock_eq_true_iff _).2
  obtain ⟨i, j, hij, hll, hlh, hhl, hhh⟩ := hcross
  refine ⟨i, j, hij, ?_, ?_, ?_, ?_⟩
  · exact (oneHighGraphPairingRefinement_multiplicity_odd_iff
      G hfree hv p hll.1).2 hll.2
  · exact (oneHighGraphPairingRefinement_multiplicity_odd_iff
      G hfree hv p hlh.1).2 hlh.2
  · exact (oneHighGraphPairingRefinement_multiplicity_odd_iff
      G hfree hv p hhl.1).2 hhl.2
  · exact (oneHighGraphPairingRefinement_multiplicity_odd_iff
      G hfree hv p hhh.1).2 hhh.2

/-- Complete one-high assembly using the capacity-covered presentation once.
The all-even branch uses the existing table certificates; the two odd-support
branches use the new exact-refinement banks.  Only the mate-miss hexagon
terminal remains structural at this interface. -/
theorem orderFortyNineStratumExcluded_one_of_capacitySectorRefinementPinBanks
    (hcheckedEven : ∀ (profile : Fin 5) table,
      table ∈ oneHighAllEvenCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (hhexagon : OneHighMateMissHexagonSectorExcluded)
    (hturnBank : OneHighThreePairTurnRefinementPinBank)
    (hcrossBank : OneHighCrossBlockRefinementPinBank) :
    OrderFortyNineStratumExcluded 1 := by
  intro G _ _ _ hfree hmin hHigh
  obtain ⟨v, hv, p, stored, hstored, hagree⟩ :=
    oneHighRawV2OrbitCover_capacityInventory G inferInstance inferInstance
      inferInstance hfree hmin hHigh
  rcases orderFortyNine_oneHigh_structural_sector_capstone
      G hfree hmin (Fintype.card_fin 49) hv p with
    heven | hmate | hthree | hfour
  · let profile : Fin 5 :=
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩
    have hstoredAll : stored ∈
        oneHighAllEvenCapacityInventoryTables profile :=
      oneHigh_storedTable_mem_allEvenCapacityInventory
        G hfree hv p heven stored hstored hagree
    have hcertStored : OneHighFamilyV2CheckedUnsat p.profile stored :=
      hcheckedEven profile stored hstoredAll
    have hcertGraph : OneHighFamilyV2CheckedUnsat p.profile
        (oneHighFamilyGraphTable
          (oneHighRelabeledLeafGraph G v
            (oneHighLeafFinFortyEquiv G hfree v
              p.branchLabel p.leafLabel)) p.profile) :=
      hcertStored.transport hagree.symm
    exact false_of_rawOneHigh_v2Checked
      G hfree hmin (Fintype.card_fin 49) hv p.unique_high p.external_empty
        p.outer_degree p.mate p.mate_involutive p.mate_adj p.branchLabel
        p.branch_mate p.leafLabel p.profile p.constraints hcertGraph
  · exact hhexagon G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p hmate
  · exact false_of_oneHigh_threePairTurn_refinementPinBank
      hturnBank G hfree hv p stored hstored hagree hthree
  · exact false_of_oneHigh_crossBlock_refinementPinBank
      hcrossBank G hfree hv p stored hstored hagree hfour

end

end Erdos85

#print axioms Erdos85.oneHighGraphPairingRefinement_mem_capacityInventoryRefinements
#print axioms Erdos85.false_of_oneHigh_capacitySector_refinementPinBank
#print axioms Erdos85.false_of_oneHigh_threePairTurn_refinementPinBank
#print axioms Erdos85.false_of_oneHigh_crossBlock_refinementPinBank
#print axioms Erdos85.orderFortyNineStratumExcluded_one_of_capacitySectorRefinementPinBanks
