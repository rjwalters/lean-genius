import Proofs.Erdos85FinalDyadicExceptionalDefectEnergyIdentity
import Proofs.Erdos85DefectPairsComplementBalance

/-!
# Signed exceptional defect-pair ledger

The signed defect quadratic is the internal defect incidence of the positive
and negative supports, minus twice their cross incidence.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Quadratic defect energy of a disjoint signed pair of finite supports. -/
theorem signedIndicator_defectEnergy_eq_pairLedger
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (F E : Finset V) (hFE : Disjoint F E) :
    (∑ v : V, (if v ∈ F then (1 : ℤ) else if v ∈ E then -1 else 0) *
        (∑ w ∈ D.neighborFinset v,
          if w ∈ F then (1 : ℤ) else if w ∈ E then -1 else 0)) =
      2 * ((supportedEdgeGraph D F).edgeFinset.card : ℤ) +
        2 * ((supportedEdgeGraph D E).edgeFinset.card : ℤ) -
        2 * ∑ v ∈ F, ((D.neighborFinset v ∩ E).card : ℤ) := by
  classical
  let z : V → ℤ := fun v =>
    if v ∈ F then 1 else if v ∈ E then -1 else 0
  have hz (v : V) :
      z v = (if v ∈ F then (1 : ℤ) else 0) -
        (if v ∈ E then (1 : ℤ) else 0) := by
    by_cases hvF : v ∈ F
    · have hvE : v ∉ E := Finset.disjoint_left.mp hFE hvF
      simp [z, hvF, hvE]
    · by_cases hvE : v ∈ E <;> simp [z, hvF, hvE]
  have hinner (v : V) :
      (∑ w ∈ D.neighborFinset v, z w) =
        ((D.neighborFinset v ∩ F).card : ℤ) -
          ((D.neighborFinset v ∩ E).card : ℤ) := by
    simp_rw [hz, Finset.sum_sub_distrib]
    simp [Finset.sum_ite_mem]
  let t : V → ℤ := fun v => z v * ∑ w ∈ D.neighborFinset v, z w
  have htF (v : V) (hv : v ∈ F) :
      t v = ((D.neighborFinset v ∩ F).card : ℤ) -
        ((D.neighborFinset v ∩ E).card : ℤ) := by
    have hvE : v ∉ E := Finset.disjoint_left.mp hFE hv
    simp [t, hz, hv, hvE]
  have htE (v : V) (hv : v ∈ E) :
      t v = -((D.neighborFinset v ∩ F).card : ℤ) +
        ((D.neighborFinset v ∩ E).card : ℤ) := by
    have hvF : v ∉ F := fun hv' => Finset.disjoint_left.mp hFE hv' hv
    simp [t, hz, hv, hvF]
    ring
  have hsupp : (∑ v : V, t v) = ∑ v ∈ F ∪ E, t v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    have hvF : v ∉ F := fun h => hv (Finset.mem_union_left E h)
    have hvE : v ∉ E := fun h => hv (Finset.mem_union_right F h)
    simp [t, hz, hvF, hvE]
  have hcross := sum_card_neighbor_inter_comm D F E
  have hFF := sum_internal_incidence_eq_twice_supported_edges D F
  have hEE := sum_internal_incidence_eq_twice_supported_edges D E
  change (∑ v : V, t v) = _
  rw [hsupp, Finset.sum_union hFE]
  have hsumF :
      (∑ v ∈ F, t v) =
        (∑ v ∈ F, ((D.neighborFinset v ∩ F).card : ℤ)) -
          ∑ v ∈ F, ((D.neighborFinset v ∩ E).card : ℤ) := by
    calc
      _ = ∑ v ∈ F,
          (((D.neighborFinset v ∩ F).card : ℤ) -
            ((D.neighborFinset v ∩ E).card : ℤ)) := by
        apply Finset.sum_congr rfl
        exact htF
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hsumE :
      (∑ v ∈ E, t v) =
        -(∑ v ∈ E, ((D.neighborFinset v ∩ F).card : ℤ)) +
          ∑ v ∈ E, ((D.neighborFinset v ∩ E).card : ℤ) := by
    calc
      _ = ∑ v ∈ E,
          (-((D.neighborFinset v ∩ F).card : ℤ) +
            ((D.neighborFinset v ∩ E).card : ℤ)) := by
        apply Finset.sum_congr rfl
        exact htE
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [hsumF, hsumE]
  have hcrossZ :
      (∑ v ∈ F, ((D.neighborFinset v ∩ E).card : ℤ)) =
        ∑ v ∈ E, ((D.neighborFinset v ∩ F).card : ℤ) := by
    exact_mod_cast hcross
  have hFFZ :
      (∑ v ∈ F, ((D.neighborFinset v ∩ F).card : ℤ)) =
        2 * ((supportedEdgeGraph D F).edgeFinset.card : ℤ) := by
    exact_mod_cast hFF
  have hEEZ :
      (∑ v ∈ E, ((D.neighborFinset v ∩ E).card : ℤ)) =
        2 * ((supportedEdgeGraph D E).edgeFinset.card : ℤ) := by
    exact_mod_cast hEE
  rw [← hcrossZ, hFFZ, hEEZ]
  ring

/-- When every positive-negative pair is a defect edge, the cross incidence
is the product of the two support sizes. -/
theorem signedIndicator_defectEnergy_eq_pairLedger_of_cross
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (F E : Finset V) (hFE : Disjoint F E)
    (hcross : ∀ ⦃v w⦄, v ∈ F → w ∈ E → D.Adj v w) :
    (∑ v : V, (if v ∈ F then (1 : ℤ) else if v ∈ E then -1 else 0) *
        (∑ w ∈ D.neighborFinset v,
          if w ∈ F then (1 : ℤ) else if w ∈ E then -1 else 0)) =
      2 * ((supportedEdgeGraph D F).edgeFinset.card : ℤ) +
        2 * ((supportedEdgeGraph D E).edgeFinset.card : ℤ) -
        2 * ((F.card : ℤ) * E.card) := by
  rw [signedIndicator_defectEnergy_eq_pairLedger D F E hFE]
  have hinter : ∀ v ∈ F, D.neighborFinset v ∩ E = E := by
    intro v hv
    apply Finset.inter_eq_right.mpr
    intro w hw
    simpa [SimpleGraph.mem_neighborFinset] using hcross hv hw
  have hsum :
      (∑ v ∈ F, ((D.neighborFinset v ∩ E).card : ℤ)) =
        (F.card : ℤ) * E.card := by
    calc
      _ = ∑ _v ∈ F, (E.card : ℤ) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hinter v hv]
      _ = _ := by simp
  rw [hsum]

/-- For the canonical exceptional sign, the full-empty defect contribution
is the exact product `|F||E|`; only the two internal defect-pair counts remain. -/
theorem exceptionalOccupancySign_defectEnergy_eq_full_empty_pairLedger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 0 < q)
    (hreg : ∀ v, G.degree v = q) (S : Finset V) :
    (∑ v : V, exceptionalOccupancySign G S q v *
        (∑ w ∈ (secondOrderDefectGraph G).neighborFinset v,
          exceptionalOccupancySign G S q w)) =
      2 * ((supportedEdgeGraph (secondOrderDefectGraph G)
          (fullLineCenters G S q)).edgeFinset.card : ℤ) +
        2 * ((supportedEdgeGraph (secondOrderDefectGraph G)
          (emptyLineCenters G S)).edgeFinset.card : ℤ) -
        2 * (((fullLineCenters G S q).card : ℤ) *
          (emptyLineCenters G S).card) := by
  let F := fullLineCenters G S q
  let E := emptyLineCenters G S
  have hz : ∀ v : V, exceptionalOccupancySign G S q v =
      if v ∈ F then (1 : ℤ) else if v ∈ E then -1 else 0 := by
    intro v
    simp [exceptionalOccupancySign, F, E]
  simp_rw [hz]
  apply signedIndicator_defectEnergy_eq_pairLedger_of_cross
  · exact fullLineCenters_disjoint_emptyLineCenters G S hq
  · intro v w hv hw
    exact binarySquare_full_empty_secondOrderDefect_adj
      G hfree hq hreg S
        ((mem_fullLineCenters G S q v).mp hv)
        ((mem_emptyLineCenters G S w).mp hw)

/-- Fully expanded final-dyadic energy census: the only geometric term is
the internal defect-edge ledger of the canonical full and empty centers. -/
theorem finalDyadic_exceptionalCensus_eq_full_empty_defectPairLedger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c) :
    (S.card : ℤ) +
        3 * (finalDyadicPositiveHighCutCenters G S q r).card +
        (finalDyadicNegativeHighCutCenters G S j r).card =
      (2 * (r : ℤ)) ^ 2 + ((q : ℤ) - 1) * c -
        (2 * ((supportedEdgeGraph (secondOrderDefectGraph G)
            (fullLineCenters G S q)).edgeFinset.card : ℤ) +
          2 * ((supportedEdgeGraph (secondOrderDefectGraph G)
            (emptyLineCenters G S)).edgeFinset.card : ℤ) -
          2 * (((fullLineCenters G S q).card : ℤ) *
            (emptyLineCenters G S).card)) := by
  rw [finalDyadic_exceptionalCensus_eq_mass_norm_sub_defectEnergy
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf hsupport]
  rw [exceptionalOccupancySign_defectEnergy_eq_full_empty_pairLedger
    G hfree (by omega) hreg S]

end

end Erdos85

#print axioms Erdos85.signedIndicator_defectEnergy_eq_pairLedger
#print axioms Erdos85.signedIndicator_defectEnergy_eq_pairLedger_of_cross
#print axioms
  Erdos85.exceptionalOccupancySign_defectEnergy_eq_full_empty_pairLedger
#print axioms
  Erdos85.finalDyadic_exceptionalCensus_eq_full_empty_defectPairLedger
