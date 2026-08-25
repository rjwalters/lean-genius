import Proofs.Erdos85OneHighOddProfileSeparatedRepeat
import Proofs.Erdos85OneHighOddProfileRepeatedOwnerLocalEdges

/-!
# Distinct keys at a shared owner across different partitions

For a four-mate-pair transversal, the key root-pair edge is complementary to
the owner root-pair edge.  Consequently two witnesses sharing an exact owner
but carrying different partition codes cannot carry the same exact key.  At a
two-edge shared branch this will force the selected internal edges to be the
two different matching edges.
-/

namespace Erdos85

/-- Finite label form of complement uniqueness: separated witnesses with a
shared owner and unequal partition codes have unequal repeated keys. -/
theorem oneHigh_sharedOwner_unequalPartitionCode_keys_ne
    (s t u : Fin 8) (key₁ key₂ : OneHighLabelPair)
    (hst : s ≠ t) (htm : t ≠ oneHighStandardMate s)
    (hsu : s ≠ u) (hum : u ≠ oneHighStandardMate s)
    (hkey₁lt : key₁.1 < key₁.2)
    (hkey₁mate : key₁.2 ≠ oneHighStandardMate key₁.1)
    (hkey₁farS : OneHighKeyFarFromSource key₁ s)
    (hkey₁farT : OneHighKeyFarFromSource key₁ t)
    (hkey₂lt : key₂.1 < key₂.2)
    (hkey₂mate : key₂.2 ≠ oneHighStandardMate key₂.1)
    (hkey₂farS : OneHighKeyFarFromSource key₂ s)
    (hkey₂farU : OneHighKeyFarFromSource key₂ u)
    (hcode : oneHighOwnerPartitionCode s t ≠
      oneHighOwnerPartitionCode s u) :
    key₁ ≠ key₂ := by
  native_decide +revert

/-- Graph-facing form: two local-edge witnesses of unequal partition codes,
oriented toward the same exact owner branch, carry distinct repeated keys.
The target-side matching-edge sources and their key equalities are retained. -/
theorem oneHigh_orientedSharedOwner_unequalCodes_targetKeys_ne
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} {c d : Fin 3}
    (q : OneHighPartitionLocalEdgeWitness G hfree hv p c)
    (r : OneHighPartitionLocalEdgeWitness G hfree hv p d)
    (htarget : q.t = r.t) (hcd : c ≠ d) :
    ∃ keyq keyr : OneHighLabelPair,
      keyq ≠ keyr ∧
      (∃ y ∈ matchingEdgeSources (oneHighInternalMate G hfree v q.t),
        (min (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj q.t y))
            (p.branchLabel (oneHighMatchedMissLabel G hfree hv
              p.external_empty p.outer_degree p.mate p.mate_adj q.t
                (oneHighInternalMate G hfree v q.t y))),
          max (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj q.t y))
            (p.branchLabel (oneHighMatchedMissLabel G hfree hv
              p.external_empty p.outer_degree p.mate p.mate_adj q.t
                (oneHighInternalMate G hfree v q.t y)))) = keyq) ∧
      (∃ y ∈ matchingEdgeSources (oneHighInternalMate G hfree v r.t),
        (min (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj r.t y))
            (p.branchLabel (oneHighMatchedMissLabel G hfree hv
              p.external_empty p.outer_degree p.mate p.mate_adj r.t
                (oneHighInternalMate G hfree v r.t y))),
          max (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj r.t y))
            (p.branchLabel (oneHighMatchedMissLabel G hfree hv
              p.external_empty p.outer_degree p.mate p.mate_adj r.t
                (oneHighInternalMate G hfree v r.t y)))) = keyr) := by
  rcases q.edge_data with ⟨keyq, hkqlt, hkqmate, hkqfarS, hkqfarT,
    xq, hxq, hxqkey, yq, hyq, hyqkey⟩
  rcases r.edge_data with ⟨keyr, hkrlt, hkrmate, hkrfarS, hkrfarT,
    xr, hxr, hxrkey, yr, hyr, hyrkey⟩
  have hqReverseMate : q.s ≠ p.mate q.t := by
    intro h
    apply q.target_ne_mate
    have hm := congrArg p.mate h
    simpa [p.mate_involutive q.t] using hm.symm
  have hrReverseMate : r.s ≠ p.mate r.t := by
    intro h
    apply r.target_ne_mate
    have hm := congrArg p.mate h
    simpa [p.mate_involutive r.t] using hm.symm
  have hqCode : oneHighOwnerPartitionCode
      (p.branchLabel q.t) (p.branchLabel q.s) = c := by
    rw [← oneHighOwnerPartitionCode_comm]
    exact of_decide_eq_true q.code_eq
  have hrCode : oneHighOwnerPartitionCode
      (p.branchLabel r.t) (p.branchLabel r.s) = d := by
    rw [← oneHighOwnerPartitionCode_comm]
    exact of_decide_eq_true r.code_eq
  have hcodeNe : oneHighOwnerPartitionCode
      (p.branchLabel q.t) (p.branchLabel q.s) ≠
      oneHighOwnerPartitionCode (p.branchLabel q.t) (p.branchLabel r.s) := by
    intro h
    apply hcd
    rw [← hqCode, ← hrCode]
    simpa [htarget] using h
  have hkeys : keyq ≠ keyr :=
    oneHigh_sharedOwner_unequalPartitionCode_keys_ne
      (p.branchLabel q.t) (p.branchLabel q.s) (p.branchLabel r.s)
      keyq keyr
      (fun h => q.source_ne (p.branchLabel.injective h.symm))
      (by
        intro h
        apply hqReverseMate
        apply p.branchLabel.injective
        simpa [p.branch_mate] using h)
      (fun h => r.source_ne (p.branchLabel.injective (htarget ▸ h).symm))
      (by
        intro h
        apply hrReverseMate
        apply p.branchLabel.injective
        simpa [p.branch_mate, htarget] using h)
      hkqlt hkqmate hkqfarT hkqfarS
      hkrlt hkrmate (by simpa [htarget] using hkrfarT) hkrfarS hcodeNe
  exact ⟨keyq, keyr, hkeys, ⟨yq, hyq, hyqkey⟩,
    ⟨yr, hyr, hyrkey⟩⟩

end Erdos85

#print axioms Erdos85.oneHigh_sharedOwner_unequalPartitionCode_keys_ne
#print axioms Erdos85.oneHigh_orientedSharedOwner_unequalCodes_targetKeys_ne
