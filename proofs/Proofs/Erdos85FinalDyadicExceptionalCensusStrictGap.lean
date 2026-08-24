import Proofs.Erdos85FinalDyadicExceptionalSignedLaplacianGap

/-!
# Strict exceptional census gap

The full/empty population equations cancel the displacement square against
the forced cross term in the signed Laplacian gap.  Preconnectedness leaves
the strict residual `+2`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the preconnected proper-even final branch, the four-level exceptional
adjacency census is at least `c² + 2`. -/
theorem finalDyadic_exceptionalCensus_sq_add_two_le
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
    (hcpos : 0 < c) (hcle : c ≤ q) (hceven : Even c) :
    (c : ℤ) ^ 2 + 2 ≤
      (S.card : ℤ) +
        3 * (finalDyadicPositiveHighCutCenters G S q r).card +
        (finalDyadicNegativeHighCutCenters G S j r).card := by
  let F := fullLineCenters G S q
  let E := emptyLineCenters G S
  have hgap :=
    binarySquare_four_full_empty_add_two_le_exceptionalSignedLaplacianGap
      G hfree hq hreg hcard hconn S hsupport hcpos hcle hceven
  change 4 * ((F.card : ℤ) * E.card) + 2 ≤ _ at hgap
  have henergy := finalDyadic_exceptionalCensus_eq_mass_norm_sub_defectEnergy
    G hfree (by omega) hqa hreg hcard S hdiv hdisp hr hrhalf hsupport
  have hqsub : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  rw [hqsub] at hgap
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

/-- Eliminating `M` with the signed high-class handshake gives a direct
strict lower bound on the positive high class. -/
theorem finalDyadic_four_positiveHighCutCenters_ge_sq_gap
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
    (hcpos : 0 < c) (hcle : c ≤ q) (hceven : Even c) :
    (c : ℤ) ^ 2 + 2 + 2 * (q : ℤ) * r - 2 * S.card ≤
      4 * (finalDyadicPositiveHighCutCenters G S q r).card := by
  have hcensus := finalDyadic_exceptionalCensus_sq_add_two_le
    G hfree hq hqa hreg hcard hconn S hdiv hdisp hr hrhalf
      hsupport hcpos hcle hceven
  have hdiff := finalDyadic_defectCutDegree_highClasses_card_sub
    G hfree (by omega) hqa hreg hcard S hdiv hdisp hr hrhalf
  nlinarith

end

end Erdos85

#print axioms Erdos85.finalDyadic_exceptionalCensus_sq_add_two_le
#print axioms Erdos85.finalDyadic_four_positiveHighCutCenters_ge_sq_gap
