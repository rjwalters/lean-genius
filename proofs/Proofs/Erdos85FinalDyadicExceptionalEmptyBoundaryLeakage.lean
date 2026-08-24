import Proofs.Erdos85FinalDyadicExceptionalCensusStrictGap

/-!
# Empty-center boundary leakage below saturation

The empty-center defect clique is joined completely to the full centers.
Thus each empty center uses `c-1` internal defect neighbors and has exactly
`q-c` defect neighbors outside an exceptional support of size `c`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every empty center contributes exactly `q-c` incidences to the boundary
of a canonical exceptional support of size `c`. -/
theorem binarySquare_empty_boundaryDegree_eq_support_deficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q c : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hcle : c ≤ q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    ∀ v ∈ emptyLineCenters G S,
      ((secondOrderDefectGraph G).neighborFinset v ∩
        ((exceptionalSignedSupport G S q)ᶜ : Finset V)).card = q - c := by
  let D := secondOrderDefectGraph G
  let B := exceptionalSignedSupport G S q
  let F := fullLineCenters G S q
  let E := emptyLineCenters G S
  have hBset : B = F ∪ E := exceptionalSignedSupport_eq_full_union_empty G S q
  have hBcard : B.card = c := hsupport
  have hDreg : ∀ v, D.degree v = q - 1 :=
    binarySquare_regular_secondOrderDefect_degree_eq
      G hfree hq hreg hcard
  intro v hvE
  have hvB : v ∈ B := by
    rw [hBset]
    exact Finset.mem_union_right F hvE
  have hinternal : D.neighborFinset v ∩ B = B.erase v := by
    ext w
    constructor
    · intro hw
      have hwData := Finset.mem_inter.mp hw
      exact Finset.mem_erase.mpr ⟨fun h => by
        subst w
        exact D.loopless.irrefl v
          ((SimpleGraph.mem_neighborFinset D v v).mp hwData.1), hwData.2⟩
    · intro hw
      have hwData := Finset.mem_erase.mp hw
      have hwUnion : w ∈ F ∪ E := by simpa [← hBset] using hwData.2
      rcases Finset.mem_union.mp hwUnion with hwF | hwE
      · have hvw := binarySquare_full_empty_secondOrderDefect_adj
          G hfree (by omega) hreg S
            ((mem_fullLineCenters G S q w).mp hwF)
            ((mem_emptyLineCenters G S v).mp hvE)
        exact Finset.mem_inter.mpr ⟨by
          simpa [D, SimpleGraph.mem_neighborFinset] using hvw.symm, hwData.2⟩
      · exact Finset.mem_inter.mpr ⟨by
          simpa [D, SimpleGraph.mem_neighborFinset] using
            hemptyClique hvE hwE hwData.1.symm, hwData.2⟩
  have hpartition :
      (D.neighborFinset v ∩ B).card +
          (D.neighborFinset v ∩ (Bᶜ : Finset V)).card = q - 1 := by
    rw [← Finset.card_union_of_disjoint]
    · have hunion :
          D.neighborFinset v ∩ B ∪
              D.neighborFinset v ∩ (Bᶜ : Finset V) =
            D.neighborFinset v := by
        ext w
        by_cases hw : w ∈ B <;> simp [hw]
      rw [hunion, D.card_neighborFinset_eq_degree, hDreg]
    · exact Finset.disjoint_left.mpr fun w hwB hwC =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp hwC).2)
          (Finset.mem_inter.mp hwB).2
  rw [hinternal, Finset.card_erase_of_mem hvB, hBcard] at hpartition
  have hcpos : 0 < c := by
    rw [← hBcard]
    exact Finset.card_pos.mpr ⟨v, hvB⟩
  have hsplitSub : q - 1 = (c - 1) + (q - c) := by omega
  change (D.neighborFinset v ∩ (Bᶜ : Finset V)).card = q - c
  omega

/-- Summing the empty-center contribution gives the canonical support
boundary lower bound `|E|(q-c)`. -/
theorem binarySquare_empty_card_mul_support_deficit_le_exceptionalBoundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q c : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hcle : c ≤ q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    (emptyLineCenters G S).card * (q - c) ≤
      shoreBoundaryIncidence (secondOrderDefectGraph G)
        (exceptionalSignedSupport G S q) := by
  have hpoint := binarySquare_empty_boundaryDegree_eq_support_deficit
    G hfree hq hreg hcard S hsupport hcle hemptyClique
  have hEsub : emptyLineCenters G S ⊆ exceptionalSignedSupport G S q := by
    rw [exceptionalSignedSupport_eq_full_union_empty]
    exact Finset.subset_union_right
  have hsum :
      (∑ v ∈ emptyLineCenters G S,
        ((secondOrderDefectGraph G).neighborFinset v ∩
          ((exceptionalSignedSupport G S q)ᶜ : Finset V)).card) =
        (emptyLineCenters G S).card * (q - c) := by
    calc
      _ = ∑ _v ∈ emptyLineCenters G S, (q - c) := by
        apply Finset.sum_congr rfl
        exact hpoint
      _ = _ := by simp
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset hEsub

/-- The empty-center leakage strengthens the energy census below saturation;
after eliminating `|E|`, the correction is `(c-2r)(q-c)`. -/
theorem finalDyadic_two_sq_add_populationDeficit_le_twice_exceptionalCensus
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hcle : c ≤ q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    2 * (c : ℤ) ^ 2 + ((c : ℤ) - 2 * r) * ((q : ℤ) - c) ≤
      2 * ((S.card : ℤ) +
        3 * (finalDyadicPositiveHighCutCenters G S q r).card +
        (finalDyadicNegativeHighCutCenters G S j r).card) := by
  let F := fullLineCenters G S q
  let E := emptyLineCenters G S
  have hgap :=
    binarySquare_exceptionalOccupancySign_laplacianGap_eq_boundary_add_four_cross
      G hfree (by omega) hreg hcard S hsupport
  change _ = shoreBoundaryIncidence (secondOrderDefectGraph G)
    (exceptionalSignedSupport G S q) + 4 * ((F.card : ℤ) * E.card) at hgap
  have hboundaryNat :=
    binarySquare_empty_card_mul_support_deficit_le_exceptionalBoundary
      G hfree (by omega) hreg hcard S hsupport hcle hemptyClique
  have hboundary : (E.card : ℤ) * (q - c : ℕ) ≤
      shoreBoundaryIncidence (secondOrderDefectGraph G)
        (exceptionalSignedSupport G S q) := by
    exact_mod_cast hboundaryNat
  have henergy := finalDyadic_exceptionalCensus_eq_mass_norm_sub_defectEnergy
    G hfree (by omega) hqa hreg hcard S hdiv hdisp hr hrhalf hsupport
  have hqsub : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  rw [hqsub] at hgap
  have hqcsub : ((q - c : ℕ) : ℤ) = (q : ℤ) - c := by
    rw [Nat.cast_sub hcle]
  rw [hqcsub] at hboundary
  have hpop := exceptionalSignedSupport_population_profile
    G S (by omega : 0 < q) hsupport
      (sum_exceptionalOccupancySign_eq_cutSign
        G (by omega) hreg S
          (finalDyadic_occupancy_trichotomy G hqa hreg S hdiv))
  rw [hdisp] at hpop
  change F.card + E.card = c ∧
    (F.card : ℤ) - E.card = 2 * r at hpop
  have hsumZ : (F.card : ℤ) + E.card = c := by
    exact_mod_cast hpop.1
  nlinarith

/-- Handshake form of the refined leakage bound, directly constraining the
positive high-cut population. -/
theorem finalDyadic_eight_positiveHighCutCenters_ge_leakageGap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hcle : c ≤ q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    2 * (c : ℤ) ^ 2 + ((c : ℤ) - 2 * r) * ((q : ℤ) - c) +
        4 * (q : ℤ) * r - 2 * (q : ℤ) ^ 2 - 4 * r ≤
      8 * (finalDyadicPositiveHighCutCenters G S q r).card := by
  have hleak :=
    finalDyadic_two_sq_add_populationDeficit_le_twice_exceptionalCensus
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hcle hemptyClique
  have hdiff := finalDyadic_defectCutDegree_highClasses_card_sub
    G hfree (by omega) hqa hreg hcard S hdiv hdisp hr hrhalf
  have hcardZ : (Fintype.card V : ℤ) = (q : ℤ) ^ 2 := by
    rw [hcard]
    push_cast
    ring
  rw [hcardZ] at hdisp
  nlinarith

end

end Erdos85

#print axioms Erdos85.binarySquare_empty_boundaryDegree_eq_support_deficit
#print axioms
  Erdos85.binarySquare_empty_card_mul_support_deficit_le_exceptionalBoundary
#print axioms
  Erdos85.finalDyadic_two_sq_add_populationDeficit_le_twice_exceptionalCensus
#print axioms
  Erdos85.finalDyadic_eight_positiveHighCutCenters_ge_leakageGap
