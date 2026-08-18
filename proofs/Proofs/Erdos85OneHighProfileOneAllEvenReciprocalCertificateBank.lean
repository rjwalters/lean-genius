import Proofs.Erdos85OneHighProfileOneAllEvenReciprocalCertificate4ee646ca0ec3e2f0
import Proofs.Erdos85OneHighProfileOneAllEvenReciprocalCertificate528457773b2abef3
import Proofs.Erdos85OneHighProfileOneAllEvenReciprocalCertificate8d35c26cc42db606
import Proofs.Erdos85OneHighProfileOneAllEvenReciprocalCertificateb6eaecad0234c0d3
import Proofs.Erdos85OneHighProfileOneAllEvenReciprocalCertificatefa91192a322d685f

/-! # Complete checked bank for the profile-1 all-even reciprocal inventory -/

namespace Erdos85

/-- The five kernel-checked certificates, in authoritative inventory order. -/
def oneHighProfileOneAllEvenReciprocalCheckedBank :
    List (OneHighFamilyV2CheckedEntry 1) :=
  [ oneHighProfileOneAllEvenReciprocalEntry4ee646ca0ec3e2f0,
    oneHighProfileOneAllEvenReciprocalEntry528457773b2abef3,
    oneHighProfileOneAllEvenReciprocalEntry8d35c26cc42db606,
    oneHighProfileOneAllEvenReciprocalEntryb6eaecad0234c0d3,
    oneHighProfileOneAllEvenReciprocalEntryfa91192a322d685f ]

/-- Proof erasure exposes exactly the authoritative five-row inventory. -/
theorem oneHighProfileOneAllEvenReciprocalCheckedBank_tables :
    oneHighFamilyV2CheckedBankTables
      oneHighProfileOneAllEvenReciprocalCheckedBank =
        oneHighProfileOneAllEvenReciprocalInventoryTables := by
  apply List.ext_get
  · simp [oneHighFamilyV2CheckedBankTables,
      oneHighProfileOneAllEvenReciprocalCheckedBank,
      oneHighProfileOneAllEvenReciprocalInventoryTables_length]
  · intro n hbank hinventory
    have hn : n < 5 := by
      simpa [oneHighFamilyV2CheckedBankTables,
        oneHighProfileOneAllEvenReciprocalCheckedBank] using hbank
    interval_cases n
    · simpa [oneHighFamilyV2CheckedBankTables,
        oneHighProfileOneAllEvenReciprocalCheckedBank,
        oneHighProfileOneAllEvenReciprocalEntry4ee646ca0ec3e2f0,
        oneHighProfileOneAllEvenReciprocalTable4ee646ca0ec3e2f0] using
        (List.head_eq_getElem
          oneHighProfileOneAllEvenReciprocalInventoryTables_nonempty)
    all_goals
      simp [oneHighFamilyV2CheckedBankTables,
        oneHighProfileOneAllEvenReciprocalCheckedBank,
        oneHighProfileOneAllEvenReciprocalEntry4ee646ca0ec3e2f0,
        oneHighProfileOneAllEvenReciprocalEntry528457773b2abef3,
        oneHighProfileOneAllEvenReciprocalEntry8d35c26cc42db606,
        oneHighProfileOneAllEvenReciprocalEntryb6eaecad0234c0d3,
        oneHighProfileOneAllEvenReciprocalEntryfa91192a322d685f,
        oneHighProfileOneAllEvenReciprocalTable4ee646ca0ec3e2f0,
        oneHighProfileOneAllEvenReciprocalTable528457773b2abef3,
        oneHighProfileOneAllEvenReciprocalTable8d35c26cc42db606,
        oneHighProfileOneAllEvenReciprocalTableb6eaecad0234c0d3,
        oneHighProfileOneAllEvenReciprocalTablefa91192a322d685f,
        oneHighProfileOneAllEvenReciprocalIndex528457773b2abef3,
        oneHighProfileOneAllEvenReciprocalIndex8d35c26cc42db606,
        oneHighProfileOneAllEvenReciprocalIndexb6eaecad0234c0d3,
        oneHighProfileOneAllEvenReciprocalIndexfa91192a322d685f]

/-- Every row in the exact profile-1 all-even reciprocal inventory has
kernel-checked exact-v2 UNSAT evidence. -/
theorem oneHighProfileOneAllEvenReciprocalInventory_checked :
    ∀ table ∈ oneHighProfileOneAllEvenReciprocalInventoryTables,
      OneHighFamilyV2CheckedUnsat 1 table := by
  intro table htable
  apply oneHighFamilyV2Checked_of_mem_bank
    oneHighProfileOneAllEvenReciprocalCheckedBank
  rw [oneHighProfileOneAllEvenReciprocalCheckedBank_tables]
  exact htable

/-- Certificate-free terminal consumer: the complete checked bank eliminates
the graph-facing profile-1 reciprocal all-even sector. -/
theorem false_of_profileOne_reciprocal_allEven_checkedBank
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
        p.profile) stored) : False :=
  false_of_profileOne_reciprocal_allEven_checked G hfree hmin q hprofile
    heven stored hstored hagree
    oneHighProfileOneAllEvenReciprocalInventory_checked

end Erdos85
