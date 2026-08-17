import Proofs.Erdos85OneHighTurnResidualReflection
import Proofs.Erdos85OneHighV2Exclusion
import Proofs.Erdos85OneHighGraphStructuralMateHexagon
import Proofs.Erdos85OneHighMultiplicitySectorSupport
import Proofs.Erdos85OneHighStructuralTerminalInterface

/-! # Ordered assembly for the same-owner three-pair-turn sector

The mate and alternating-cross tests are intentionally performed before the
residual inventory lookup.  Consequently the certificate obligation below is
only the correlation-preserving 7,433-row residual, rather than the original
9,707-row saturated-turn inventory.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Close a same-owner pinned turn by checking, in order, the odd-mate sector,
the alternating-cross sector, and finally the checked residual inventory.

The first two hypotheses are graph-local callbacks.  This formulation keeps
the ordering independent of the eventual structural terminal implementations,
while the final branch is already connected all the way to the raw graph CNF.
-/
theorem false_of_sameOwnerPinnedThreePairTurn_orderedResidual
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p)
    (howner : T.qAB.sourceEdge.1 = T.qBC.sourceEdge.1)
    (table : OneHighMissTable)
    (hcapacity : table ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v
            p.branchLabel p.leafLabel)) p.profile) table)
    (hmate : oneHighRefinementHasOddMateKey
      (oneHighGraphPairingRefinement G hfree hv p) = true → False)
    (hcross : oneHighRefinementHasOddCrossBlock
      (oneHighGraphPairingRefinement G hfree hv p) = true → False)
    (hchecked : ∀ stored,
      stored ∈ oneHighSaturatedOddTurnResidualInventoryTables
        ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ →
      OneHighFamilyV2CheckedUnsat p.profile stored) : False := by
  cases hmateEq : oneHighRefinementHasOddMateKey
      (oneHighGraphPairingRefinement G hfree hv p) with
  | true => exact hmate hmateEq
  | false =>
      cases hcrossEq : oneHighRefinementHasOddCrossBlock
          (oneHighGraphPairingRefinement G hfree hv p) with
      | true => exact hcross hcrossEq
      | false =>
          have hmem := T.mem_saturatedOddTurnResidualInventory
            G hfree hv p howner hmateEq hcrossEq table hcapacity hagree
          have hcert : OneHighFamilyV2CheckedUnsat p.profile
              (oneHighFamilyGraphTable
                (oneHighRelabeledLeafGraph G v
                  (oneHighLeafFinFortyEquiv G hfree v
                    p.branchLabel p.leafLabel)) p.profile) :=
            (hchecked table hmem).transport hagree.symm
          exact false_of_rawOneHigh_v2Checked
            G hfree hmin hcard hv p.unique_high p.external_empty
              p.outer_degree p.mate p.mate_involutive p.mate_adj
              p.branchLabel p.branch_mate p.leafLabel p.profile
              p.constraints hcert

/-- The structural-terminal specialization of the ordered assembly.  An odd
mate bit is transported to the global multiplicity and hence to a mate-miss
hexagon; an odd cross bit is transported to the global cross-block support.
Only when both bits are false is a residual SAT certificate requested. -/
theorem false_of_sameOwnerPinnedThreePairTurn_of_structuralTerminals
    (hhexagon : OneHighMateMissHexagonSectorExcluded)
    (hcrossTerminal : OneHighCrossBlockSectorExcluded)
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : Fin 49} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p)
    (howner : T.qAB.sourceEdge.1 = T.qBC.sourceEdge.1)
    (table : OneHighMissTable)
    (hcapacity : table ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v
            p.branchLabel p.leafLabel)) p.profile) table)
    (hchecked : ∀ stored,
      stored ∈ oneHighSaturatedOddTurnResidualInventoryTables
        ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ →
      OneHighFamilyV2CheckedUnsat p.profile stored) : False := by
  let refinement := oneHighGraphPairingRefinement G hfree hv p
  let multiplicity := exchangedMissPairMultiplicity
    (oneHighGlobalInternalMate G hfree v)
    (fun x => p.branchLabel
      (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj x))
  have hoddGlobal {a b : Fin 8}
      (hlt : (oneHighCanonicalLabelPair a b).1 <
        (oneHighCanonicalLabelPair a b).2)
      (hodd : Odd (oneHighPairingRefinementMultiplicity refinement
        (oneHighCanonicalLabelPair a b))) :
      Odd (multiplicity (oneHighCanonicalLabelPair a b)) := by
    dsimp [refinement, multiplicity] at hodd ⊢
    rw [← oneHighGraphPairingRefinementMultiplicity_eq_global
      G hfree hv p _ hlt]
    exact hodd
  apply false_of_sameOwnerPinnedThreePairTurn_orderedResidual
    G hfree hmin (Fintype.card_fin 49) hv p T howner table
      hcapacity hagree
  · intro hmate
    have href : OneHighRefinementOddMateKeyProp refinement :=
      (oneHighRefinementHasOddMateKey_eq_true_iff refinement).mp hmate
    have hglobal : OneHighMultiplicityOddMateKeyProp multiplicity := by
      obtain ⟨i, hi⟩ := href
      refine ⟨i, hoddGlobal ?_ hi⟩
      fin_cases i <;> decide
    have hsupport := oneHighMultiplicityOddMateKey_oddSupport hglobal
    exact hhexagon G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p
        (exists_oneHighMateMissHexagon_of_structuralMateSector
          G hfree hv p hsupport)
  · intro hcross
    have href : OneHighRefinementOddCrossBlockProp refinement :=
      (oneHighRefinementHasOddCrossBlock_eq_true_iff refinement).mp hcross
    have hglobal : OneHighMultiplicityOddCrossBlockProp multiplicity := by
      obtain ⟨i, j, hij, hll, hlh, hhl, hhh⟩ := href
      refine ⟨i, j, hij, hoddGlobal ?_ hll, hoddGlobal ?_ hlh,
        hoddGlobal ?_ hhl, hoddGlobal ?_ hhh⟩ <;>
        simp [oneHighCanonicalLabelPair, oneHighStandardPairLow,
          oneHighStandardPairHigh] <;> omega
    exact hcrossTerminal G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p
        (oneHighMultiplicityOddCrossBlock_oddSupport hglobal)
  · exact hchecked

end

end Erdos85
