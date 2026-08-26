import Proofs.Erdos85OneHighAllEvenSingletonInventory
import Proofs.Erdos85OneHighAllEvenSectorTerminal
import Proofs.Erdos85OneHighGraphPairingMultiplicity
import Proofs.Erdos85OneHighPairingSectorReflection
import Proofs.Erdos85OneHighV2CapacityCover

/-! # Profile-one all-even reciprocal inventory terminal -/

namespace Erdos85

noncomputable section

/-- Canonical symmetric restriction determined by the inventory's 24 upper
coordinates. -/
def oneHighPairingTableRestrict (table : OneHighMissTable) : OneHighMissTable :=
  fun c j =>
    if c < 8 ∧ j < 8 ∧ c ≠ j ∧ j ≠ c ^^^ 1 then
      oneHighFamilyTableGet table c j
    else 0

/-- Restricting both sides of relevant-coordinate agreement gives literal
table equality.  This is the transport interface needed by predicates whose
implementation inspects compatible pairing refinements. -/
theorem oneHighPairingTableRestrict_eq_of_relevantAgree
    {left right : OneHighMissTable}
    (hagree : OneHighTableRelevantAgree left right) :
    oneHighPairingTableRestrict left = oneHighPairingTableRestrict right := by
  funext c j
  by_cases h : c < 8 ∧ j < 8 ∧ c ≠ j ∧ j ≠ c ^^^ 1
  · have hmem : (min c j, max c j) ∈ oneHighFamilyTablePairs := by
      rcases h with ⟨hc, hj, hne, hmate⟩
      interval_cases c <;> interval_cases j <;>
        simp_all <;> decide
    change (if c < 8 ∧ j < 8 ∧ c ≠ j ∧ j ≠ c ^^^ 1 then
        oneHighFamilyTableGet left c j else 0) =
      (if c < 8 ∧ j < 8 ∧ c ≠ j ∧ j ≠ c ^^^ 1 then
        oneHighFamilyTableGet right c j else 0)
    rw [if_pos h, if_pos h]
    simpa [oneHighFamilyTableGet] using hagree _ hmem
  · simp [oneHighPairingTableRestrict, h]

/-- The graph-relevant table is already in the canonical restricted form. -/
theorem oneHighTableRestrict_graphRelevantMissTable
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj] (profile : Nat) :
    oneHighPairingTableRestrict (oneHighGraphRelevantMissTable R profile) =
      oneHighGraphRelevantMissTable R profile := by
  funext c j
  by_cases h : c < 8 ∧ j < 8 ∧ c ≠ j ∧ j ≠ c ^^^ 1
  · let source : Fin 8 := ⟨c, h.1⟩
    let label : Fin 8 := ⟨j, h.2.1⟩
    have hget := oneHighFamilyTableGet_graphRelevantMissTable R profile
      source label
    simpa [oneHighPairingTableRestrict, oneHighGraphRelevantMissTable, h,
      source, label] using hget
  · simp [oneHighPairingTableRestrict, oneHighGraphRelevantMissTable, h]

/-- Relevant agreement with the full graph table is equivalently available
for its pairing-facing restricted table. -/
theorem oneHighGraphRelevantMissTable_relevantAgree_of_graphTable
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj] (profile : Nat)
    {stored : OneHighMissTable}
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable R profile) stored) :
    OneHighTableRelevantAgree
      (oneHighGraphRelevantMissTable R profile) stored := by
  intro pair hpair
  have hp := oneHighFamilyTablePairs_mem_bounds hpair
  have hcond : pair.1 < 8 ∧ pair.2 < 8 ∧ pair.1 ≠ pair.2 ∧
      pair.2 ≠ pair.1 ^^^ 1 :=
    ⟨hp.1, hp.2.1, Nat.ne_of_lt hp.2.2.1, hp.2.2.2⟩
  have hle : pair.1 ≤ pair.2 := Nat.le_of_lt hp.2.2.1
  simpa [oneHighGraphRelevantMissTable, hcond, oneHighFamilyTableGet,
    Nat.min_eq_left hle, Nat.max_eq_right hle] using hagree pair hpair

/-- The actual graph pairing refinement is all-even whenever every exchanged
miss-pair key has even graph multiplicity. -/
theorem oneHighGraphPairingRefinement_allOffDiagonalEven
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key)) :
    oneHighRefinementAllOffDiagonalEven
      (oneHighGraphPairingRefinement G hfree hv p) = true := by
  rw [oneHighRefinementAllOffDiagonalEven_eq_true_iff]
  intro pair hpair hne
  have hle : pair.1 ≤ pair.2 := by
    rw [oneHighCanonicalLabelPairs, List.mem_flatMap] at hpair
    obtain ⟨i, _, hpair⟩ := hpair
    rw [List.mem_filterMap] at hpair
    obtain ⟨j, _, hpair⟩ := hpair
    split at hpair
    · next hij =>
      simp only [Option.some.injEq] at hpair
      subst pair
      exact hij
    · simp at hpair
  have hlt : pair.1 < pair.2 := lt_of_le_of_ne hle hne
  rw [oneHighGraphPairingRefinementMultiplicity_eq_global
    G hfree hv p pair hlt]
  apply heven pair
  simp [exchangedMissPairKeys, hlt]

/-- A transport-stable version of the profile-one all-even reciprocal
inventory predicate. -/
def oneHighProfileOneHasAllEvenReciprocalSingleton
    (table : OneHighMissTable) : Bool :=
  oneHighTableHasSourceZeroDiagonalSingleton 1
      (oneHighPairingTableRestrict table) &&
    oneHighTableHasAllEvenPairing 1 (oneHighPairingTableRestrict table)

def oneHighProfileOneAllEvenReciprocalInventoryTables :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables 1).filter
    oneHighProfileOneHasAllEvenReciprocalSingleton

/-- Only five capacity-orbit rows survive the profile-one reciprocal and
all-even constraints. -/
theorem oneHighProfileOneAllEvenReciprocalInventoryTables_length :
    oneHighProfileOneAllEvenReciprocalInventoryTables.length = 5 := by
  native_decide

theorem oneHighProfileOneHasAllEvenReciprocalSingleton_of_relevantAgree
    {left right : OneHighMissTable}
    (hagree : OneHighTableRelevantAgree left right)
    (hleft : oneHighProfileOneHasAllEvenReciprocalSingleton left = true) :
    oneHighProfileOneHasAllEvenReciprocalSingleton right = true := by
  unfold oneHighProfileOneHasAllEvenReciprocalSingleton at hleft ⊢
  rw [← oneHighPairingTableRestrict_eq_of_relevantAgree hagree]
  exact hleft

/-- Graph-facing profile-one terminal: a reciprocal same-miss pair in the
all-even sector forces the exact five-row executable signature. -/
theorem OneHighReciprocalSameMissEdges.graphTable_profileOneHasAllEvenReciprocalSingleton
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 1)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key)) :
    oneHighProfileOneHasAllEvenReciprocalSingleton
      (oneHighGraphRelevantMissTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) = true := by
  let table := oneHighGraphRelevantMissTable
    (oneHighRelabeledLeafGraph G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)) p.profile
  have hrestrict : oneHighPairingTableRestrict table = table :=
    oneHighTableRestrict_graphRelevantMissTable _ _
  have hrefinement := oneHighGraphPairingRefinement_mem G hfree hv p
  have hrefEven := oneHighGraphPairingRefinement_allOffDiagonalEven
    G hfree hv p heven
  have hallEven : oneHighTableHasAllEvenPairing p.profile table = true :=
    oneHighTableHasAllEvenPairing_of_refinement hrefinement hrefEven
  have hsingleton := q.graphTable_has_sourceZeroDiagonalSingleton (by omega)
  unfold oneHighProfileOneHasAllEvenReciprocalSingleton
  rw [hrestrict]
  rw [Bool.and_eq_true]
  simpa [table, hprofile] using And.intro hsingleton hallEven

/-- A stored capacity representative agreeing with the graph lies in the
five-row profile-one inventory. -/
theorem OneHighReciprocalSameMissEdges.storedTable_mem_profileOneAllEvenInventory
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 1)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key))
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables 1)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored) :
    stored ∈ oneHighProfileOneAllEvenReciprocalInventoryTables := by
  rw [oneHighProfileOneAllEvenReciprocalInventoryTables, List.mem_filter]
  refine ⟨hstored, ?_⟩
  apply oneHighProfileOneHasAllEvenReciprocalSingleton_of_relevantAgree
    (oneHighGraphRelevantMissTable_relevantAgree_of_graphTable _ _ hagree)
  exact q.graphTable_profileOneHasAllEvenReciprocalSingleton hprofile heven

/-- Checked UNSAT evidence for the exact five rows eliminates the complete
profile-one reciprocal all-even sector. -/
theorem false_of_profileOne_reciprocal_allEven_checked
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {v : Fin 49} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 1)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key))
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables 1)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored)
    (hchecked : ∀ table ∈ oneHighProfileOneAllEvenReciprocalInventoryTables,
      OneHighFamilyV2CheckedUnsat 1 table) : False := by
  have hmem := q.storedTable_mem_profileOneAllEvenInventory
    hprofile heven stored hstored hagree
  have hcertStored : OneHighFamilyV2CheckedUnsat p.profile stored := by
    simpa [hprofile] using hchecked stored hmem
  have hcertGraph : OneHighFamilyV2CheckedUnsat p.profile
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) :=
    hcertStored.transport hagree.symm
  exact false_of_rawOneHigh_v2Checked
    G hfree hmin (Fintype.card_fin 49) hv p.unique_high p.external_empty
      p.outer_degree p.mate p.mate_involutive p.mate_adj p.branchLabel
      p.branch_mate p.leafLabel p.profile p.constraints hcertGraph

end

end Erdos85
