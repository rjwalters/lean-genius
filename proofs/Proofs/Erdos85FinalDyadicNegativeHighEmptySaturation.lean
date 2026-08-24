import Proofs.Erdos85FinalDyadicPositiveHighPairPacking

/-!
# Saturation of negative-high centers by empty centers

The coupled positive-high/full-defect packing forces `q|E| ≤ |M|`.
Conversely, every negative-high center has exactly one empty neighbor, while
each empty center has degree `q`.  Hence `|M| = q|E|`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The coupled pair packing and exact energy census force at least `q`
negative-high centers per empty center. -/
theorem finalDyadic_q_mul_empty_le_negativeHigh
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
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    q * (emptyLineCenters G S).card ≤
      (finalDyadicNegativeHighCutCenters G S j r).card := by
  let F := fullLineCenters G S q
  let E := emptyLineCenters G S
  let P := finalDyadicPositiveHighCutCenters G S q r
  let M := finalDyadicNegativeHighCutCenters G S j r
  let eF := (supportedEdgeGraph (secondOrderDefectGraph G) F).edgeFinset.card
  have hpack :=
    finalDyadic_positiveHigh_add_fullDefectPairs_le_full_choose_two
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
  change P.card + (secondOrderDefectPairs G F).card ≤ F.card.choose 2 at hpack
  rw [← supportedSecondOrder_edge_card_eq_defectPairs G F] at hpack
  change P.card + eF ≤ F.card.choose 2 at hpack
  have hpackZ : (P.card : ℤ) + eF ≤ (F.card.choose 2 : ℕ) := by
    exact_mod_cast hpack
  have hchooseF := two_mul_natChoose_two_cast F.card
  have hchooseE := two_mul_natChoose_two_cast E.card
  have heq := finalDyadic_twice_fullDefectEdges_eq_exceptionalCensusResidual
    G hfree (by omega) hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique
  change 2 * (eF : ℤ) =
    (2 * (r : ℤ)) ^ 2 + ((q : ℤ) - 1) * c -
      ((S.card : ℤ) + 3 * (P.card : ℤ) + M.card) -
      2 * (E.card.choose 2 : ℕ) +
      2 * ((F.card : ℤ) * E.card) at heq
  have hdiff := finalDyadic_defectCutDegree_highClasses_card_sub
    G hfree (by omega) hqa hreg hcard S hdiv hdisp hr hrhalf
  change (P.card : ℤ) - M.card = 2 * (q : ℤ) * r - S.card at hdiff
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
  have hlowerZ : (q : ℤ) * E.card ≤ M.card := by
    nlinarith
  exact_mod_cast hlowerZ

/-- Every negative-high center has exactly one empty-center neighbor. -/
theorem finalDyadic_negativeHigh_exact_empty_neighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j) :
    ∀ v ∈ finalDyadicNegativeHighCutCenters G S j r,
      (G.neighborFinset v ∩ emptyLineCenters G S).card = 1 := by
  let F := fullLineCenters G S q
  let E := emptyLineCenters G S
  intro v hvM
  have hvNotS : v ∉ S := Finset.mem_compl.mp (Finset.mem_filter.mp hvM).1
  have hfullZero : (G.neighborFinset v ∩ F).card = 0 := by
    by_contra hzero
    have hpos : 0 < (G.neighborFinset v ∩ F).card :=
      Nat.pos_of_ne_zero hzero
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    have hwData := Finset.mem_inter.mp hw
    have hwFull := (mem_fullLineCenters G S q w).mp hwData.2
    have hvNw : v ∈ G.neighborFinset w := by
      exact (G.mem_neighborFinset w v).mpr
        ((G.mem_neighborFinset v w).mp hwData.1).symm
    have hNwEq : G.neighborFinset w ∩ S = G.neighborFinset w := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [G.card_neighborFinset_eq_degree, hreg]
      omega
    have hvInter : v ∈ G.neighborFinset w ∩ S := by
      rw [hNwEq]
      exact hvNw
    exact hvNotS (Finset.mem_inter.mp hvInter).2
  have hbalance := finalDyadic_negativeShore_exceptionalAdjacencyBalance
    G hfree (by omega) hqa hreg hcard S hdiv hdisp hr hrhalf v hvNotS
  change finalDyadicExceptionalAdjacencyBalance G S q v =
    if v ∈ finalDyadicNegativeHighCutCenters G S j r then -1 else 0 at hbalance
  rw [if_pos hvM] at hbalance
  have hz (w : V) : exceptionalOccupancySign G S q w =
      (if w ∈ F then (1 : ℤ) else 0) -
        (if w ∈ E then (1 : ℤ) else 0) := by
    have hdisj := fullLineCenters_disjoint_emptyLineCenters G S (by omega : 0 < q)
    by_cases hwF : w ∈ F
    · have hwE : w ∉ E := Finset.disjoint_left.mp hdisj hwF
      simp [exceptionalOccupancySign, F, E, hwF, hwE,
        (mem_fullLineCenters G S q w).mp hwF]
    · by_cases hwE : w ∈ E
      · have hoccE := (mem_emptyLineCenters G S w).mp hwE
        have hzeroNotQ : ¬ 0 = q := by omega
        simp [exceptionalOccupancySign, F, E, hwF, hwE, hoccE, hzeroNotQ]
      · have hnotFull : ¬(G.neighborFinset w ∩ S).card = q := fun h =>
          hwF ((mem_fullLineCenters G S q w).mpr h)
        have hnotEmpty : ¬(G.neighborFinset w ∩ S).card = 0 := fun h =>
          hwE ((mem_emptyLineCenters G S w).mpr h)
        simp [exceptionalOccupancySign, F, E, hwF, hwE, hnotFull, hnotEmpty]
  change (∑ w ∈ G.neighborFinset v, exceptionalOccupancySign G S q w) = -1
    at hbalance
  simp_rw [hz, Finset.sum_sub_distrib] at hbalance
  have hcounts : ((G.neighborFinset v ∩ F).card : ℤ) -
      (G.neighborFinset v ∩ E).card = -1 := by
    simpa [Finset.sum_ite_mem] using hbalance
  change (G.neighborFinset v ∩ E).card = 1
  change (G.neighborFinset v ∩ F).card = 0 at hfullZero
  omega

/-- Degree incidence gives the reverse bound `|M| ≤ q|E|`. -/
theorem finalDyadic_negativeHigh_le_q_mul_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j) :
    (finalDyadicNegativeHighCutCenters G S j r).card ≤
      q * (emptyLineCenters G S).card := by
  let M := finalDyadicNegativeHighCutCenters G S j r
  let E := emptyLineCenters G S
  have hprofile := finalDyadic_negativeHigh_exact_empty_neighbor
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
  have hleft : (∑ v ∈ M, (G.neighborFinset v ∩ E).card) = M.card := by
    calc
      _ = ∑ _v ∈ M, 1 := by
        apply Finset.sum_congr rfl
        exact hprofile
      _ = _ := by simp
  have hcomm := sum_card_neighbor_inter_comm G M E
  have hright : (∑ e ∈ E, (G.neighborFinset e ∩ M).card) ≤ q * E.card := by
    calc
      _ ≤ ∑ _e ∈ E, q := by
        apply Finset.sum_le_sum
        intro e _
        calc
          (G.neighborFinset e ∩ M).card ≤ (G.neighborFinset e).card :=
            Finset.card_le_card Finset.inter_subset_left
          _ = q := by rw [G.card_neighborFinset_eq_degree, hreg]
      _ = q * E.card := by simp [Nat.mul_comm]
  change M.card ≤ q * E.card
  rw [← hleft, hcomm]
  exact hright

/-- Exact saturation: the negative-high class is the full degree incidence
mass of the empty centers. -/
theorem finalDyadic_negativeHigh_card_eq_q_mul_empty
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
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    (finalDyadicNegativeHighCutCenters G S j r).card =
      q * (emptyLineCenters G S).card := by
  apply Nat.le_antisymm
  · exact finalDyadic_negativeHigh_le_q_mul_empty
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
  · exact finalDyadic_q_mul_empty_le_negativeHigh
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique

end

end Erdos85

#print axioms Erdos85.finalDyadic_q_mul_empty_le_negativeHigh
#print axioms Erdos85.finalDyadic_negativeHigh_exact_empty_neighbor
#print axioms Erdos85.finalDyadic_negativeHigh_le_q_mul_empty
#print axioms Erdos85.finalDyadic_negativeHigh_card_eq_q_mul_empty
