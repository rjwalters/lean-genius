import Proofs.Erdos85OneHighV2CapacityInventory
import Proofs.Erdos85OneHighV2F3bRawLedger

/-!
# Sound capacity-filtered cover for the one-high inventory

This file discharges the graph-to-filter gate: the table extracted from every
raw one-high presentation satisfies cross-miss capacity, relevant-coordinate
agreement preserves that predicate, and hence the established orbit cover
lands in the 13,351-row filtered inventory.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Raw F3b geometry gives the exact target cardinality read by the capacity
filter. -/
theorem oneHighFamilyV2F3b_card_eq_of_rawGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (pair : Nat × Nat) (hpair : pair ∈ oneHighFamilyTablePairs) :
    let E := oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    (oneHighEncodedCommonPairBlock R
      ⟨pair.1, (oneHighFamilyTablePairs_mem_bounds hpair).1⟩
      ⟨pair.2, (oneHighFamilyTablePairs_mem_bounds hpair).2.1⟩).card =
      20 + oneHighFamilyTableGet (oneHighFamilyGraphTable R p.profile)
        pair.1 (pair.2 ^^^ 1) +
      oneHighFamilyTableGet (oneHighFamilyGraphTable R p.profile)
        pair.2 (pair.1 ^^^ 1) := by
  intro E R
  have hp := oneHighFamilyTablePairs_mem_bounds hpair
  let a : Fin 8 := ⟨pair.1, hp.1⟩
  let b : Fin 8 := ⟨pair.2, hp.2.1⟩
  let s := p.branchLabel.symm a
  let t := p.branchLabel.symm b
  have hts : t ≠ s := by
    intro h
    have this : b = a := p.branchLabel.symm.injective h
    exact (Nat.ne_of_lt hp.2.2.1) (congrArg Fin.val this).symm
  have htm : t ≠ p.mate s := by
    intro h
    have hb : b = oneHighStandardMate a := by
      calc
        b = p.branchLabel t := by simp [t]
        _ = p.branchLabel (p.mate s) := congrArg p.branchLabel h
        _ = oneHighStandardMate (p.branchLabel s) := p.branch_mate s
        _ = oneHighStandardMate a := by simp [s]
    have hvb := congrArg Fin.val hb
    rw [oneHighStandardMate_val_eq_xor] at hvb
    exact hp.2.2.2 hvb
  have hmateT_ne_s : p.mate t ≠ s := by
    intro h
    apply htm
    rw [← h, p.mate_involutive t]
  have hmateT_ne_mateS : p.mate t ≠ p.mate s := by
    intro h
    exact hts (p.mate_involutive.injective h)
  have hmateS_ne_t : p.mate s ≠ t := Ne.symm htm
  have hmateS_ne_mateT : p.mate s ≠ p.mate t := Ne.symm hmateT_ne_mateS
  have hraw := card_oneHighEncodedCommonPairBlock_eq_twenty_add_missCounts
    G hfree hmin hcard hv p.unique_high p.external_empty p.outer_degree
      p.mate p.mate_involutive p.mate_adj p.branchLabel p.leafLabel
      s t hts htm
  have htab₁ := oneHighFamilyGraphTable_eq_highBranchMissCount
    G hfree v p.mate p.branchLabel p.branch_mate p.leafLabel
      p.profile p.constraints s (p.mate t) hmateT_ne_s hmateT_ne_mateS
  have htab₂ := oneHighFamilyGraphTable_eq_highBranchMissCount
    G hfree v p.mate p.branchLabel p.branch_mate p.leafLabel
      p.profile p.constraints t (p.mate s) hmateS_ne_t hmateS_ne_mateT
  have hlabelS : p.branchLabel s = a := p.branchLabel.apply_symm_apply a
  have hlabelT : p.branchLabel t = b := p.branchLabel.apply_symm_apply b
  have hlabelMateS : (p.branchLabel (p.mate s)).val = pair.1 ^^^ 1 := by
    rw [p.branch_mate s, oneHighStandardMate_val_eq_xor, hlabelS]
  have hlabelMateT : (p.branchLabel (p.mate t)).val = pair.2 ^^^ 1 := by
    rw [p.branch_mate t, oneHighStandardMate_val_eq_xor, hlabelT]
  have hlabelMateS' : (p.branchLabel (p.mate s)).val =
      (p.branchLabel s).val ^^^ 1 := by
    rw [p.branch_mate s, oneHighStandardMate_val_eq_xor]
  have hlabelMateT' : (p.branchLabel (p.mate t)).val =
      (p.branchLabel t).val ^^^ 1 := by
    rw [p.branch_mate t, oneHighStandardMate_val_eq_xor]
  have hj₁c : p.branchLabel (p.mate t) ≠ p.branchLabel s := fun h =>
    hmateT_ne_s (p.branchLabel.injective h)
  have hj₁m : p.branchLabel (p.mate t) ≠
      oneHighStandardMate (p.branchLabel s) := by
    rw [← p.branch_mate s]
    exact fun h => hmateT_ne_mateS (p.branchLabel.injective h)
  have hj₂c : p.branchLabel (p.mate s) ≠ p.branchLabel t := fun h =>
    hmateS_ne_t (p.branchLabel.injective h)
  have hj₂m : p.branchLabel (p.mate s) ≠
      oneHighStandardMate (p.branchLabel t) := by
    rw [← p.branch_mate t]
    exact fun h => hmateS_ne_mateT (p.branchLabel.injective h)
  have hget₁ := oneHighFamilyTableGet_graphTable_eq p.profile R
    p.constraints (p.branchLabel s) (p.branchLabel (p.mate t)) hj₁c hj₁m
  have hget₂ := oneHighFamilyTableGet_graphTable_eq p.profile R
    p.constraints (p.branchLabel t) (p.branchLabel (p.mate s)) hj₂c hj₂m
  change (oneHighEncodedCommonPairBlock R a b).card = _
  rw [← hlabelS, ← hlabelT]
  rw [← show (p.branchLabel s).val = pair.1 from congrArg Fin.val hlabelS,
    ← show (p.branchLabel t).val = pair.2 from congrArg Fin.val hlabelT,
    ← hlabelMateT', ← hlabelMateS']
  rw [hget₁, hget₂, htab₁, htab₂]
  simpa [E, R, s, t, a, b] using hraw

/-- Every graph-derived exact-v2 table passes the executable cross-miss
capacity filter. -/
theorem OneHighRawV2Presentation.graphTable_crossMissCapacity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) :
    let E := oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    oneHighTableCrossMissCapacity
      (oneHighFamilyGraphTable R p.profile) = true := by
  intro E R
  unfold oneHighTableCrossMissCapacity
  rw [List.all_eq_true]
  intro pair hpair
  simp only [decide_eq_true_eq]
  have heq := oneHighFamilyV2F3b_card_eq_of_rawGraph
    G hfree hmin hcard hv p pair hpair
  dsimp only at heq
  let a : Fin 8 := ⟨pair.1, (oneHighFamilyTablePairs_mem_bounds hpair).1⟩
  let b : Fin 8 := ⟨pair.2, (oneHighFamilyTablePairs_mem_bounds hpair).2.1⟩
  have hsubset : oneHighEncodedCommonPairBlock R a b ⊆
      (oneHighFamilyBlockFinset a).product (oneHighFamilyBlockFinset b) :=
    Finset.filter_subset _ _
  have hle := Finset.card_le_card hsubset
  simp [Finset.card_product, oneHighFamilyBlockFinset_card] at hle
  have heq' : (oneHighEncodedCommonPairBlock R a b).card =
      20 + oneHighFamilyTableGet (oneHighFamilyGraphTable R p.profile)
        pair.1 (pair.2 ^^^ 1) +
      oneHighFamilyTableGet (oneHighFamilyGraphTable R p.profile)
        pair.2 (pair.1 ^^^ 1) := by
    simpa [E, R, a, b] using heq
  omega

/-- Relevant-coordinate agreement transports a successful capacity test. -/
theorem oneHighTableCrossMissCapacity_of_agree
    {left right : OneHighMissTable}
    (h : OneHighTableRelevantAgree left right)
    (hleft : oneHighTableCrossMissCapacity left = true) :
    oneHighTableCrossMissCapacity right = true := by
  unfold oneHighTableCrossMissCapacity at hleft ⊢
  rw [List.all_eq_true] at hleft ⊢
  intro pair hp
  have hl : left (min pair.1 (pair.2 ^^^ 1))
      (max pair.1 (pair.2 ^^^ 1)) =
      right (min pair.1 (pair.2 ^^^ 1))
        (max pair.1 (pair.2 ^^^ 1)) := by
    exact h _ (oneHighFamilyTablePairs_f3bLeft_mem pair hp)
  have hr : left (min pair.2 (pair.1 ^^^ 1))
      (max pair.2 (pair.1 ^^^ 1)) =
      right (min pair.2 (pair.1 ^^^ 1))
        (max pair.2 (pair.1 ^^^ 1)) := by
    exact h _ (oneHighFamilyTablePairs_f3bRight_mem pair hp)
  simpa [oneHighFamilyTableGet, hl, hr] using hleft pair hp

/-- The established raw orbit cover lands in the capacity-filtered inventory. -/
theorem oneHighRawV2OrbitCover_capacityInventory :
    OneHighRawV2OrbitCover oneHighCapacityInventoryTables := by
  intro G _ _ _ hfree hmin hHigh
  obtain ⟨v, hv, p, table, hmem, hagree⟩ :=
    oneHighRawV2OrbitCover_inventory G inferInstance inferInstance
      inferInstance hfree hmin hHigh
  refine ⟨v, hv, p, table, ?_, hagree⟩
  rw [oneHighCapacityInventoryTables, List.mem_filter]
  refine ⟨hmem, ?_⟩
  have hgraph := p.graphTable_crossMissCapacity G hfree hmin
    (Fintype.card_fin 49) hv
  dsimp only at hgraph
  exact oneHighTableCrossMissCapacity_of_agree hagree hgraph

/-- Only the 13,351 capacity-compatible rows now require checked UNSAT
evidence to exclude the complete one-high stratum. -/
theorem orderFortyNineStratumExcluded_one_of_capacityInventory_checked
    (hchecked : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table) :
    OrderFortyNineStratumExcluded 1 :=
  orderFortyNineStratumExcluded_one_of_rawV2OrbitCover
    oneHighRawV2OrbitCover_capacityInventory hchecked

end

end Erdos85
