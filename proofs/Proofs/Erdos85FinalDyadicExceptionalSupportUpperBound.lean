import Proofs.Erdos85FinalDyadicEmptyBlockCrossDefect
import Proofs.Erdos85FinalDyadicExceptionalCensusStrictGap

/-!
# Automatic upper bound for the final exceptional support

Cross-block routing bounds the empty population by `2^j-r`.  The canonical
population equations then force the exceptional support size to be at most
`q`, discharging a formerly external hypothesis of the strict census gap.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The final exceptional support automatically has size at most `q`. -/
theorem finalDyadic_exceptionalSignedSupport_card_le_q
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
    c ≤ q := by
  let F := fullLineCenters G S q
  let E := emptyLineCenters G S
  have hE := finalDyadic_emptyLineCenters_card_le_half_sub_r
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique
  change E.card ≤ 2 ^ j - r at hE
  have hsum := exceptionalSignedSupport_card_eq_full_add_empty
    G S (by omega : 0 < q)
  rw [hsupport] at hsum
  change c = F.card + E.card at hsum
  have hdiff := finalDyadic_full_sub_empty_eq_cutDisplacement
    G hqa hreg S hdiv
  rw [hdisp] at hdiff
  change (F.card : ℤ) - E.card = 2 * r at hdiff
  have hdiffNat : F.card = E.card + 2 * r := by omega
  omega

/-- Strict exceptional census gap with the support upper bound discharged by
the empty-block routing theorem. -/
theorem finalDyadic_exceptionalCensus_sq_add_two_le_of_emptyClique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hcpos : 0 < c) (hceven : Even c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    (c : ℤ) ^ 2 + 2 ≤
      (S.card : ℤ) +
        3 * (finalDyadicPositiveHighCutCenters G S q r).card +
        (finalDyadicNegativeHighCutCenters G S j r).card := by
  have hcle := finalDyadic_exceptionalSignedSupport_card_le_q
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique
  exact finalDyadic_exceptionalCensus_sq_add_two_le
    G hfree hq hqa hreg hcard hconn S hdiv hdisp hr hrhalf
      hsupport hcpos hcle hceven

/-- Direct positive-high lower bound with `c ≤ q` discharged. -/
theorem finalDyadic_four_positiveHighCutCenters_ge_sq_gap_of_emptyClique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hcpos : 0 < c) (hceven : Even c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    (c : ℤ) ^ 2 + 2 + 2 * (q : ℤ) * r - 2 * S.card ≤
      4 * (finalDyadicPositiveHighCutCenters G S q r).card := by
  have hcle := finalDyadic_exceptionalSignedSupport_card_le_q
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique
  exact finalDyadic_four_positiveHighCutCenters_ge_sq_gap
    G hfree hq hqa hreg hcard hconn S hdiv hdisp hr hrhalf
      hsupport hcpos hcle hceven

end

end Erdos85

#print axioms Erdos85.finalDyadic_exceptionalSignedSupport_card_le_q
#print axioms
  Erdos85.finalDyadic_exceptionalCensus_sq_add_two_le_of_emptyClique
#print axioms
  Erdos85.finalDyadic_four_positiveHighCutCenters_ge_sq_gap_of_emptyClique
