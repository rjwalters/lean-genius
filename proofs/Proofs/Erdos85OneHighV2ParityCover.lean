import Proofs.Erdos85OneHighV2ParityInventory
import Proofs.Erdos85OneHighV2CapacityCover
import Proofs.Erdos85OneHighSameMissParityConsumer

/-! # Graph-side socket for the parity-filtered one-high cover

This module isolates the remaining structural obstruction exactly: if the
global internally matched miss-label function has no nonconstant edge, the
already certified capacity cover lands in the 87-row parity inventory.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Vanishing of the global nonconstant-edge source set makes the canonical
miss table of a raw presentation pass the executable even-entry test. -/
theorem oneHighTableEntriesEven_of_nonconstantSources_eq_empty
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G) {v : Fin 49}
    (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hempty : nonconstantMatchingEdgeSources
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj) = ∅) :
    let E := oneHighLeafFinFortyEquiv G hfree v
      p.branchLabel p.leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    oneHighTableEntriesEven
      (oneHighFamilyGraphTable R p.profile) = true := by
  intro E R
  unfold oneHighTableEntriesEven
  rw [List.all_eq_true]
  intro pair hpair
  simp only [decide_eq_true_eq]
  have hp := oneHighFamilyTablePairs_mem_bounds hpair
  let s := p.branchLabel.symm (⟨pair.1, hp.1⟩ : Fin 8)
  let u := p.branchLabel.symm (⟨pair.2, hp.2.1⟩ : Fin 8)
  have hus : u ≠ s := by
    intro h
    have heq : (⟨pair.2, hp.2.1⟩ : Fin 8) = ⟨pair.1, hp.1⟩ :=
      p.branchLabel.symm.injective h
    exact (Nat.ne_of_lt hp.2.2.1) (congrArg Fin.val heq).symm
  have hum : u ≠ p.mate s := by
    intro h
    have heq : (⟨pair.2, hp.2.1⟩ : Fin 8) =
        oneHighStandardMate (⟨pair.1, hp.1⟩ : Fin 8) := by
      calc
        (⟨pair.2, hp.2.1⟩ : Fin 8) = p.branchLabel u := by simp [u]
        _ = p.branchLabel (p.mate s) := congrArg p.branchLabel h
        _ = oneHighStandardMate (p.branchLabel s) := p.branch_mate s
        _ = oneHighStandardMate (⟨pair.1, hp.1⟩ : Fin 8) := by simp [s]
    have hval := congrArg Fin.val heq
    have hmateVal : ∀ b : Fin 8,
        (oneHighStandardMate b).val = b.val ^^^ 1 := by
      intro b
      fin_cases b <;> decide
    rw [hmateVal] at hval
    exact hp.2.2.2 hval
  have huMem : u ∈ ((Finset.univ.erase s).erase (p.mate s)) := by
    simp [hus, hum]
  have hEven := even_highBranchMissCount_of_nonconstantSources_eq_empty
    G hfree hv p.external_empty p.mate p.mate_adj p.outer_degree hempty
      s u huMem
  have htable := oneHighFamilyGraphTable_eq_highBranchMissCount
    G hfree v p.mate p.branchLabel p.branch_mate p.leafLabel p.profile
      p.constraints s u hus hum
  rw [← htable] at hEven
  simpa [E, R, s, u] using hEven

/-- Exact structural-to-finite reduction for the one-high stratum.  The sole
remaining hypothesis says that every raw presentation has no nonconstant
internally matched miss-label edge. -/
theorem oneHighRawV2OrbitCover_parityCapacity_of_nonconstantSources_empty
    (hcapacity : OneHighRawV2OrbitCover oneHighCapacityInventoryTables)
    (hempty :
      ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
        (_ : DecidableRel (antipodalGraph G).Adj)
        (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
        (hfree : ¬ containsC4 (Fin 49) G) →
        (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
        (hHigh : (orderFortyNineHighVertices G).card = 1) →
        ∀ {v : Fin 49} (hv : G.degree v = 8)
          (p : OneHighRawV2Presentation G hfree v),
          nonconstantMatchingEdgeSources
            (oneHighGlobalInternalMate G hfree v)
            (oneHighGlobalMissLabel G hfree hv p.external_empty
              p.outer_degree p.mate p.mate_adj) = ∅) :
    OneHighRawV2OrbitCover oneHighParityCapacityInventoryTables := by
  apply oneHighRawV2OrbitCover_parityCapacity_of_graphTable_even
    hcapacity
  intro G _ _ _ hfree hmin hHigh v hv p
  exact oneHighTableEntriesEven_of_nonconstantSources_eq_empty
    G hfree hv p (hempty G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p)

/-- Specialization using the checked finite capacity inventory cover. -/
theorem oneHighRawV2OrbitCover_parityCapacity_of_nonconstantSources_empty_checked
    (hempty :
      ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
        (_ : DecidableRel (antipodalGraph G).Adj)
        (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
        (hfree : ¬ containsC4 (Fin 49) G) →
        (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
        (hHigh : (orderFortyNineHighVertices G).card = 1) →
        ∀ {v : Fin 49} (hv : G.degree v = 8)
          (p : OneHighRawV2Presentation G hfree v),
          nonconstantMatchingEdgeSources
            (oneHighGlobalInternalMate G hfree v)
            (oneHighGlobalMissLabel G hfree hv p.external_empty
              p.outer_degree p.mate p.mate_adj) = ∅) :
    OneHighRawV2OrbitCover oneHighParityCapacityInventoryTables :=
  oneHighRawV2OrbitCover_parityCapacity_of_nonconstantSources_empty
    oneHighRawV2OrbitCover_capacityInventory hempty

end

end Erdos85
