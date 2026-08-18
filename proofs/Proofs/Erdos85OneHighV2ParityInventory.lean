import Proofs.Erdos85OneHighV2CapacityInventory
import Proofs.Erdos85OneHighSameMissParity

/-! # Parity-filtered one-high orbit inventory

The same-miss principle forces every relevant directed miss-table entry to be
even.  Intersecting that executable predicate with the already certified
cross-miss capacity inventory leaves only 87 orbit representatives.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Executable parity test on the 24 stored upper non-mate entries. -/
def oneHighTableEntriesEven (table : OneHighMissTable) : Bool :=
  oneHighFamilyTablePairs.all fun pair =>
    decide (Even (table pair.1 pair.2))

/-- The graph-capacity inventory restricted to even miss tables. -/
def oneHighParityCapacityInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter oneHighTableEntriesEven

theorem oneHighParityCapacityInventoryTables_length_zero :
    (oneHighParityCapacityInventoryTables 0).length = 19 := by
  native_decide

theorem oneHighParityCapacityInventoryTables_length_one :
    (oneHighParityCapacityInventoryTables 1).length = 0 := by
  native_decide

theorem oneHighParityCapacityInventoryTables_length_two :
    (oneHighParityCapacityInventoryTables 2).length = 50 := by
  native_decide

theorem oneHighParityCapacityInventoryTables_length_three :
    (oneHighParityCapacityInventoryTables 3).length = 0 := by
  native_decide

theorem oneHighParityCapacityInventoryTables_length_four :
    (oneHighParityCapacityInventoryTables 4).length = 18 := by
  native_decide

theorem oneHighParityCapacityInventory_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighParityCapacityInventoryTables profile).length).sum = 87 := by
  native_decide

/-- Relevant-coordinate agreement transports the parity predicate. -/
theorem oneHighTableEntriesEven_of_agree
    {left right : OneHighMissTable}
    (h : OneHighTableRelevantAgree left right)
    (hleft : oneHighTableEntriesEven left = true) :
    oneHighTableEntriesEven right = true := by
  unfold oneHighTableEntriesEven at hleft ⊢
  rw [List.all_eq_true] at hleft ⊢
  intro pair hp
  simp only [decide_eq_true_eq] at hleft ⊢
  have heq := h pair hp
  rw [← heq]
  exact hleft pair hp

/-- If every graph-derived canonical table passes the parity test, the
existing graph-to-capacity cover lands in the exact 87-row inventory. -/
theorem oneHighRawV2OrbitCover_parityCapacity_of_graphTable_even
    (hcapacity : OneHighRawV2OrbitCover oneHighCapacityInventoryTables)
    (hgraphEven :
      ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
        (_ : DecidableRel (antipodalGraph G).Adj)
        (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
        (hfree : ¬ containsC4 (Fin 49) G) →
        (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
        (hHigh : (orderFortyNineHighVertices G).card = 1) →
        ∀ {v : Fin 49} (hv : G.degree v = 8)
          (p : OneHighRawV2Presentation G hfree v),
          let E := oneHighLeafFinFortyEquiv G hfree v
            p.branchLabel p.leafLabel
          let R := oneHighRelabeledLeafGraph G v E
          oneHighTableEntriesEven
            (oneHighFamilyGraphTable R p.profile) = true) :
    OneHighRawV2OrbitCover oneHighParityCapacityInventoryTables := by
  intro G _ _ _ hfree hmin hHigh
  obtain ⟨v, hv, p, table, hmem, hagree⟩ :=
    hcapacity G inferInstance inferInstance
      inferInstance hfree hmin hHigh
  refine ⟨v, hv, p, table, ?_, hagree⟩
  rw [oneHighParityCapacityInventoryTables, List.mem_filter]
  refine ⟨hmem, ?_⟩
  have hp := hgraphEven G inferInstance inferInstance inferInstance
    hfree hmin hHigh hv p
  dsimp only at hp
  exact oneHighTableEntriesEven_of_agree hagree hp

end

end Erdos85
