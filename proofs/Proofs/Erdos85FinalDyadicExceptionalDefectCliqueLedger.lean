import Proofs.Erdos85FinalDyadicExceptionalDefectPairLedger

/-!
# Minority-clique exceptional defect ledger

When the canonical empty centers form a clique in the second-order defect
graph, their internal edge term is the full binomial coefficient.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A clique has every canonical second-order defect pair. -/
theorem secondOrderDefectPairs_eq_powersetCard_of_clique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (E : Finset V)
    (hclique : ∀ ⦃u v⦄, u ∈ E → v ∈ E → u ≠ v →
      (secondOrderDefectGraph G).Adj u v) :
    secondOrderDefectPairs G E = E.powersetCard 2 := by
  apply Finset.Subset.antisymm
    (secondOrderDefectPairs_subset_powersetCard G E)
  intro T hT
  simp only [secondOrderDefectPairs, Finset.mem_filter]
  refine ⟨hT, ?_⟩
  have hTE := (Finset.mem_powersetCard.mp hT).1
  intro u hu v hv huv
  exact hclique (hTE hu) (hTE hv) huv

/-- The supported defect graph of a defect clique has the complete edge
count `choose(|E|,2)`. -/
theorem supportedSecondOrderDefect_edgeFinset_card_eq_choose_of_clique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (E : Finset V)
    (hclique : ∀ ⦃u v⦄, u ∈ E → v ∈ E → u ≠ v →
      (secondOrderDefectGraph G).Adj u v) :
    (supportedEdgeGraph (secondOrderDefectGraph G) E).edgeFinset.card =
      E.card.choose 2 := by
  have h := congrArg Finset.card
    (secondOrderDefectPairs_eq_powersetCard_of_clique G E hclique)
  rw [Finset.card_powersetCard] at h
  rw [supportedSecondOrder_edge_card_eq_defectPairs G E]
  exact h

/-- Under the canonical minority-clique hypothesis, the final exceptional
census retains only the internal defect edges among full centers. -/
theorem finalDyadic_exceptionalCensus_eq_fullDefectPair_minorityCliqueLedger
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
    (S.card : ℤ) +
        3 * (finalDyadicPositiveHighCutCenters G S q r).card +
        (finalDyadicNegativeHighCutCenters G S j r).card =
      (2 * (r : ℤ)) ^ 2 + ((q : ℤ) - 1) * c -
        (2 * ((supportedEdgeGraph (secondOrderDefectGraph G)
            (fullLineCenters G S q)).edgeFinset.card : ℤ) +
          2 * (((emptyLineCenters G S).card.choose 2 : ℕ) : ℤ) -
          2 * (((fullLineCenters G S q).card : ℤ) *
            (emptyLineCenters G S).card)) := by
  rw [finalDyadic_exceptionalCensus_eq_full_empty_defectPairLedger
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf hsupport]
  rw [supportedSecondOrderDefect_edgeFinset_card_eq_choose_of_clique
    G (emptyLineCenters G S) hemptyClique]

end

end Erdos85

#print axioms Erdos85.secondOrderDefectPairs_eq_powersetCard_of_clique
#print axioms
  Erdos85.supportedSecondOrderDefect_edgeFinset_card_eq_choose_of_clique
#print axioms
  Erdos85.finalDyadic_exceptionalCensus_eq_fullDefectPair_minorityCliqueLedger
