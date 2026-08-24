import Proofs.Erdos85FinalDyadicExceptionalDefectCliqueLedger

/-!
# Exact full-center defect-pair census

After the empty-center clique term is collapsed, the energy identity solves
exactly for twice the number of defect edges internal to the full centers.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Internal second-order defect edges cannot exceed all unordered pairs of
their finite support. -/
theorem supportedSecondOrderDefect_edgeFinset_card_le_choose
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (B : Finset V) :
    (supportedEdgeGraph (secondOrderDefectGraph G) B).edgeFinset.card ≤
      B.card.choose 2 := by
  rw [supportedSecondOrder_edge_card_eq_defectPairs G B]
  calc
    (secondOrderDefectPairs G B).card ≤ (B.powersetCard 2).card :=
      Finset.card_le_card (secondOrderDefectPairs_subset_powersetCard G B)
    _ = B.card.choose 2 := Finset.card_powersetCard 2 B

/-- The final-dyadic census solves exactly for twice the internal full-center
defect-edge count. -/
theorem finalDyadic_twice_fullDefectEdges_eq_exceptionalCensusResidual
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
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    2 * ((supportedEdgeGraph (secondOrderDefectGraph G)
        (fullLineCenters G S q)).edgeFinset.card : ℤ) =
      (2 * (r : ℤ)) ^ 2 + ((q : ℤ) - 1) * c -
        ((S.card : ℤ) +
          3 * (finalDyadicPositiveHighCutCenters G S q r).card +
          (finalDyadicNegativeHighCutCenters G S j r).card) -
        2 * (((emptyLineCenters G S).card.choose 2 : ℕ) : ℤ) +
        2 * (((fullLineCenters G S q).card : ℤ) *
          (emptyLineCenters G S).card) := by
  have h := finalDyadic_exceptionalCensus_eq_fullDefectPair_minorityCliqueLedger
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf hsupport hemptyClique
  ring_nf at h ⊢
  omega

/-- Consequently the explicit census residual is nonnegative, even, and at
most twice the number of unordered full-center pairs. -/
theorem finalDyadic_exceptionalCensusResidual_bounds_even
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
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    let R : ℤ :=
      (2 * (r : ℤ)) ^ 2 + ((q : ℤ) - 1) * c -
        ((S.card : ℤ) +
          3 * (finalDyadicPositiveHighCutCenters G S q r).card +
          (finalDyadicNegativeHighCutCenters G S j r).card) -
        2 * (((emptyLineCenters G S).card.choose 2 : ℕ) : ℤ) +
        2 * (((fullLineCenters G S q).card : ℤ) *
          (emptyLineCenters G S).card)
    0 ≤ R ∧
      R ≤ 2 * (((fullLineCenters G S q).card.choose 2 : ℕ) : ℤ) ∧
      Even R := by
  dsimp only
  let eF := (supportedEdgeGraph (secondOrderDefectGraph G)
    (fullLineCenters G S q)).edgeFinset.card
  have heq := finalDyadic_twice_fullDefectEdges_eq_exceptionalCensusResidual
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf hsupport hemptyClique
  change 2 * (eF : ℤ) = _ at heq
  have hle := supportedSecondOrderDefect_edgeFinset_card_le_choose
    G (fullLineCenters G S q)
  change eF ≤ (fullLineCenters G S q).card.choose 2 at hle
  have hleZ : (eF : ℤ) ≤
      ((fullLineCenters G S q).card.choose 2 : ℕ) := by
    exact_mod_cast hle
  constructor
  · omega
  constructor
  · omega
  · refine ⟨(eF : ℤ), ?_⟩
    omega

end

end Erdos85

#print axioms
  Erdos85.finalDyadic_twice_fullDefectEdges_eq_exceptionalCensusResidual
#print axioms
  Erdos85.supportedSecondOrderDefect_edgeFinset_card_le_choose
#print axioms Erdos85.finalDyadic_exceptionalCensusResidual_bounds_even
