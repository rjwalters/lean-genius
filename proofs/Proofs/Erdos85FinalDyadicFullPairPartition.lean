import Proofs.Erdos85FinalDyadicNegativeHighEmptySaturation

/-!
# Partition of full-center pairs

Negative-high/empty saturation forces equality in the coupled forbidden
cherry bound: every unordered pair of full centers is either a positive-high
cherry or a second-order defect pair.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The positive-high cherries and internal full-center defect pairs exhaust
all unordered full-center pairs. -/
theorem finalDyadic_positiveHigh_add_fullDefectPairs_eq_full_choose_two
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
    (finalDyadicPositiveHighCutCenters G S q r).card +
        (secondOrderDefectPairs G (fullLineCenters G S q)).card =
      (fullLineCenters G S q).card.choose 2 := by
  let F := fullLineCenters G S q
  let E := emptyLineCenters G S
  let P := finalDyadicPositiveHighCutCenters G S q r
  let M := finalDyadicNegativeHighCutCenters G S j r
  let eF := (supportedEdgeGraph (secondOrderDefectGraph G) F).edgeFinset.card
  have hle := finalDyadic_positiveHigh_add_fullDefectPairs_le_full_choose_two
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
  change P.card + (secondOrderDefectPairs G F).card ≤ F.card.choose 2 at hle
  rw [← supportedSecondOrder_edge_card_eq_defectPairs G F] at hle
  change P.card + eF ≤ F.card.choose 2 at hle
  have hleZ : (P.card : ℤ) + eF ≤ (F.card.choose 2 : ℕ) := by
    exact_mod_cast hle
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
  have hME := finalDyadic_negativeHigh_card_eq_q_mul_empty
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique
  change M.card = q * E.card at hME
  have hMEZ : (M.card : ℤ) = (q : ℤ) * E.card := by exact_mod_cast hME
  have heqZ : (P.card : ℤ) + eF = (F.card.choose 2 : ℕ) := by
    nlinarith
  have heqNat : P.card + eF = F.card.choose 2 := by exact_mod_cast heqZ
  change P.card + (secondOrderDefectPairs G F).card = F.card.choose 2
  rw [← supportedSecondOrder_edge_card_eq_defectPairs G F]
  exact heqNat

/-- Equality in the forbidden-cherry bound: all full-center cherries are
centered at positive-high vertices. -/
theorem finalDyadic_sum_fullNeighbor_choose_two_eq_positiveHigh
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
    (∑ v : V,
      ((G.neighborFinset v ∩ fullLineCenters G S q).card).choose 2) =
      (finalDyadicPositiveHighCutCenters G S q r).card := by
  let F := fullLineCenters G S q
  let P := finalDyadicPositiveHighCutCenters G S q r
  let Z := secondOrderDefectPairs G F
  have hpartition :=
    finalDyadic_positiveHigh_add_fullDefectPairs_eq_full_choose_two
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique
  change P.card + Z.card = F.card.choose 2 at hpartition
  have hprofile := finalDyadic_positiveHigh_exact_full_empty_neighbor_profile
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
  have hsumP :
      (∑ v ∈ P, ((G.neighborFinset v ∩ F).card).choose 2) = P.card := by
    calc
      _ = ∑ _v ∈ P, 1 := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvTwo := (hprofile v hv).1
        change (G.neighborFinset v ∩ F).card = 2 at hvTwo
        rw [hvTwo]
        decide
      _ = _ := by simp
  have hlower : P.card ≤
      ∑ v : V, ((G.neighborFinset v ∩ F).card).choose 2 := by
    rw [← hsumP]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ P)
  have hupper := sum_choose_card_neighbor_inter_le_choose_card_sub_forbidden
    G hfree F Z
      (secondOrderDefectPairs_subset_powersetCard G F)
      (secondOrderDefectPairs_forbidden_commonNeighbor G hfree F)
  change (∑ v : V, ((G.neighborFinset v ∩ F).card).choose 2) ≤
    F.card.choose 2 - Z.card at hupper
  change (∑ v : V, ((G.neighborFinset v ∩ F).card).choose 2) = P.card
  omega

/-- Equality rigidity: outside the positive-high class, every vertex has at
most one full-center neighbor. -/
theorem finalDyadic_fullNeighbor_card_le_one_of_not_positiveHigh
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
        (secondOrderDefectGraph G).Adj u v)
    (v : V) (hv : v ∉ finalDyadicPositiveHighCutCenters G S q r) :
    (G.neighborFinset v ∩ fullLineCenters G S q).card ≤ 1 := by
  let F := fullLineCenters G S q
  let P := finalDyadicPositiveHighCutCenters G S q r
  let f : V → ℕ := fun x => ((G.neighborFinset x ∩ F).card).choose 2
  have htotal := finalDyadic_sum_fullNeighbor_choose_two_eq_positiveHigh
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique
  change (∑ x : V, f x) = P.card at htotal
  have hprofile := finalDyadic_positiveHigh_exact_full_empty_neighbor_profile
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
  have hsumP : (∑ x ∈ P, f x) = P.card := by
    calc
      _ = ∑ _x ∈ P, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxTwo := (hprofile x hx).1
        change (G.neighborFinset x ∩ F).card = 2 at hxTwo
        simp [f, hxTwo]
      _ = _ := by simp
  have hdisj : Disjoint P {v} := by
    exact Finset.disjoint_singleton_right.mpr hv
  have hsmall : (∑ x ∈ P ∪ {v}, f x) ≤ ∑ x : V, f x :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_union hdisj, hsumP] at hsmall
  simp only [Finset.sum_singleton] at hsmall
  have hfzero : f v = 0 := by omega
  change (G.neighborFinset v ∩ F).card ≤ 1
  by_contra hnot
  have htwo : 2 ≤ (G.neighborFinset v ∩ F).card := by omega
  have hpos := Nat.choose_pos htwo
  change 0 < f v at hpos
  omega

end

end Erdos85

#print axioms
  Erdos85.finalDyadic_positiveHigh_add_fullDefectPairs_eq_full_choose_two
#print axioms Erdos85.finalDyadic_sum_fullNeighbor_choose_two_eq_positiveHigh
#print axioms Erdos85.finalDyadic_fullNeighbor_card_le_one_of_not_positiveHigh
