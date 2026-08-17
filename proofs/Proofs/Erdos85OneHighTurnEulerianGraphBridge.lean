import Proofs.Erdos85OneHighTurnNonSameOwnerParityInventory
import Proofs.Erdos85OneHighGraphStructuralSector

/-! # Graph bridge for the one-high Eulerian turn inventory -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The graph-induced pairing refinement has even off-diagonal incidence at
every relabeled miss label.  Diagonal refinement pairs are deliberately
discarded: the corresponding global exchanged-multiplicity key is empty. -/
theorem oneHighGraphPairingRefinement_offDiagonal_incidence_even
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (hneigh : ∀ y, G.Adj v y → G.degree y = 7)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (p : OneHighRawV2Presentation G hfree v) :
    ∀ label : Fin 8, Even (∑ other : Fin 8,
      if other = label then 0 else
        oneHighPairingRefinementMultiplicity
          (oneHighGraphPairingRefinement G hfree hv p)
          (oneHighCanonicalLabelPair label other)) := by
  intro label
  let globalLabel := fun x => p.branchLabel
    (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
      p.mate p.mate_adj x)
  have hsum :
      (∑ other : Fin 8,
        if other = label then 0 else
          oneHighPairingRefinementMultiplicity
            (oneHighGraphPairingRefinement G hfree hv p)
            (oneHighCanonicalLabelPair label other)) =
      ∑ other : Fin 8,
        exchangedMissPairMultiplicity
          (oneHighGlobalInternalMate G hfree v) globalLabel
          (min label other, max label other) := by
    apply Finset.sum_congr rfl
    intro other _
    by_cases hother : other = label
    · subst other
      simp only [ite_true, min_self, max_self]
      symm
      exact exchangedMissPairMultiplicity_diagonal_eq_zero
        (oneHighGlobalInternalMate G hfree v) globalLabel label
    · simp only [hother, ite_false, oneHighCanonicalLabelPair]
      rw [oneHighGraphPairingRefinementMultiplicity_eq_global
        G hfree hv p (min label other, max label other)
        (min_lt_max.mpr (Ne.symm hother))]
  rw [hsum]
  exact even_oneHighGraphExchangedMultiplicity_incidence
    G hfree hv hneigh hlocal p label

/-- A graph turn transported to a capacity representative belongs to the
Eulerian parity inventory.  This is the graph-level soundness endpoint for
the executable abstraction. -/
theorem OneHighPinnedThreePairTurn.mem_nonSameOwnerOddTurnAndEulerianStateInventory
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (hneigh : ∀ y, G.Adj v y → G.degree y = 7)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
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
    table ∈ oneHighNonSameOwnerOddTurnAndEulerianStateInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ := by
  have hrefinement :=
    oneHighGraphPairingRefinement_mem_restrict_graphTable G hfree hv p
  rw [oneHighTableRestrict_eq_of_relevantAgree hagree] at hrefinement
  exact mem_oneHighNonSameOwnerOddTurnAndEulerianStateInventoryTables_of_refinement
    hcapacity hrefinement
      (T.graphPairingRefinement_hasNonSameOwnerOddTurn
        G hfree hv p hsector)
      (oneHighGraphPairingRefinement_offDiagonal_incidence_even
        G hfree hv hneigh hlocal p)

end

end Erdos85
