import Proofs.Erdos85OneHighV2Exclusion
import Proofs.Erdos85OneHighRawPresentation

/-! # Orbit-cover socket for the exact v2 one-high formula -/

namespace Erdos85

open SimpleGraph

/-- A finite list covers a PURE family profile when it contains the miss table
induced by every semantic family graph.  Orbit-enumerator verification is the
intended source of this proposition. -/
def OneHighFamilyV2TableCover
    (profile : Nat) (tables : List OneHighMissTable) : Prop :=
  ∀ (R : SimpleGraph (Fin 40)) (_ : DecidableRel R.Adj),
    OneHighPureFamilyCnfConstraints profile R →
      ∃ table ∈ tables, oneHighFamilyGraphTable R profile = table

/-- Select checked v2 UNSAT evidence for the table induced by a covered PURE
family graph. -/
theorem oneHighFamilyV2CheckedUnsat_of_tableCover
    {profile : Nat} {tables : List OneHighMissTable}
    (hcover : OneHighFamilyV2TableCover profile tables)
    (hchecked : ∀ table ∈ tables,
      OneHighFamilyV2CheckedUnsat profile table)
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints profile R) :
    OneHighFamilyV2CheckedUnsat profile
      (oneHighFamilyGraphTable R profile) := by
  rcases hcover R inferInstance hc with ⟨table, hmem, htable⟩
  simpa [htable] using hchecked table hmem

/-- A covered, checked table contradicts a raw canonical one-high
presentation.  This is the reusable endpoint beneath the order-49 terminal. -/
theorem false_of_rawOneHigh_v2TableCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {w : V}, G.degree w = 8 → w = v)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateInv : Function.Involutive mate)
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (profile : Nat)
    (hc : OneHighPureFamilyCnfConstraints profile
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel)))
    {tables : List OneHighMissTable}
    (hcover : OneHighFamilyV2TableCover profile tables)
    (hchecked : ∀ table ∈ tables,
      OneHighFamilyV2CheckedUnsat profile table) : False := by
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let R := oneHighRelabeledLeafGraph G v E
  have hcert : OneHighFamilyV2CheckedUnsat profile
      (oneHighFamilyGraphTable R profile) :=
    oneHighFamilyV2CheckedUnsat_of_tableCover hcover hchecked R hc
  exact false_of_rawOneHigh_v2Checked
    G hfree hmin hcard hv hunique hexternal houterDegree mate hmateInv
      hmateAdj branchLabel hbranchMate leafLabel profile hc hcert

/-- Five independently covered exact-v2 profile lists exclude the complete
one-high order-49 stratum. -/
theorem orderFortyNineStratumExcluded_one_of_v2TableCovers
    {tables0 tables1 tables2 tables3 tables4 : List OneHighMissTable}
    (hcover0 : OneHighFamilyV2TableCover 0 tables0)
    (hcover1 : OneHighFamilyV2TableCover 1 tables1)
    (hcover2 : OneHighFamilyV2TableCover 2 tables2)
    (hcover3 : OneHighFamilyV2TableCover 3 tables3)
    (hcover4 : OneHighFamilyV2TableCover 4 tables4)
    (hchecked0 : ∀ table ∈ tables0, OneHighFamilyV2CheckedUnsat 0 table)
    (hchecked1 : ∀ table ∈ tables1, OneHighFamilyV2CheckedUnsat 1 table)
    (hchecked2 : ∀ table ∈ tables2, OneHighFamilyV2CheckedUnsat 2 table)
    (hchecked3 : ∀ table ∈ tables3, OneHighFamilyV2CheckedUnsat 3 table)
    (hchecked4 : ∀ table ∈ tables4, OneHighFamilyV2CheckedUnsat 4 table) :
    OrderFortyNineStratumExcluded 1 := by
  intro G _ _ _ hfree hmin hHigh
  have hnonempty : (orderFortyNineHighVertices G).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨v, hvMem⟩ := hnonempty
  have hv : G.degree v = 8 := by
    simpa [orderFortyNineHighVertices] using hvMem
  obtain ⟨mate, branchLabel, leafLabel, profile, hmateInv, hmateAdj,
      hbranchMate, hprofile, hunique, hexternal, houterDegree, hc⟩ :=
    orderFortyNine_exists_rawOneHighPresentation
      G hfree hmin (Fintype.card_fin 49) hHigh hv
  interval_cases profile
  · exact false_of_rawOneHigh_v2TableCover
      G hfree hmin (Fintype.card_fin 49) hv hunique hexternal houterDegree
        mate hmateInv hmateAdj branchLabel hbranchMate leafLabel 0 hc
        hcover0 hchecked0
  · exact false_of_rawOneHigh_v2TableCover
      G hfree hmin (Fintype.card_fin 49) hv hunique hexternal houterDegree
        mate hmateInv hmateAdj branchLabel hbranchMate leafLabel 1 hc
        hcover1 hchecked1
  · exact false_of_rawOneHigh_v2TableCover
      G hfree hmin (Fintype.card_fin 49) hv hunique hexternal houterDegree
        mate hmateInv hmateAdj branchLabel hbranchMate leafLabel 2 hc
        hcover2 hchecked2
  · exact false_of_rawOneHigh_v2TableCover
      G hfree hmin (Fintype.card_fin 49) hv hunique hexternal houterDegree
        mate hmateInv hmateAdj branchLabel hbranchMate leafLabel 3 hc
        hcover3 hchecked3
  · exact false_of_rawOneHigh_v2TableCover
      G hfree hmin (Fintype.card_fin 49) hv hunique hexternal houterDegree
        mate hmateInv hmateAdj branchLabel hbranchMate leafLabel 4 hc
        hcover4 hchecked4

end Erdos85
