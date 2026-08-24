import Proofs.Erdos85CanonicalExceptionalSaturatedDeficit
import Proofs.Erdos85DyadicStoppingSupportDefectPenalizedCherrySqueeze

/-!
# Defect-pair penalty from an exceptional minority clique

A second-order-defect clique contained in a marked set contributes every
one of its two-subsets to the canonical defect-pair penalty.  The saturated
canonical exceptional profile turns the empty-line population into the
explicit parameter `r`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A defect clique `E` contained in `C` contributes at least
`choose |E| 2` canonical defect pairs inside `C`. -/
theorem choose_two_le_secondOrderDefectPairs_of_clique_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (E C : Finset V) (hEC : E ⊆ C)
    (hclique : ∀ ⦃u v⦄, u ∈ E → v ∈ E → u ≠ v →
      (secondOrderDefectGraph G).Adj u v) :
    E.card.choose 2 ≤ (secondOrderDefectPairs G C).card := by
  have hsub : E.powersetCard 2 ⊆ secondOrderDefectPairs G C := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    rw [secondOrderDefectPairs, Finset.mem_filter,
      Finset.mem_powersetCard]
    refine ⟨⟨hT.1.trans hEC, hT.2⟩, ?_⟩
    intro u hu v hv huv
    exact hclique (hT.1 hu) (hT.1 hv) huv
  simpa only [Finset.card_powersetCard] using Finset.card_le_card hsub

/-- At saturated exceptional deficit `r`, any marked set containing the
canonical empty family pays at least `choose r 2` defect pairs. -/
theorem saturatedDeficit_choose_two_le_secondOrderDefectPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {q r : ℕ} (hq : 0 < q) (hreg : ∀ x, G.degree x = q)
    (S C : Finset V)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hemptyC : emptyLineCenters G S ⊆ C)
    (hsupportCard : (exceptionalSignedSupport G S q).card = q)
    (hdisplacement :
      2 * (S.card : ℤ) - Fintype.card V = (q : ℤ) - 2 * r) :
    r.choose 2 ≤ (secondOrderDefectPairs G C).card := by
  have hsum : (fullLineCenters G S q).card +
      (emptyLineCenters G S).card = q := by
    rw [← exceptionalSignedSupport_card_eq_full_add_empty G S hq,
      hsupportCard]
  have hdiff : ((fullLineCenters G S q).card : ℤ) -
      (emptyLineCenters G S).card = (q : ℤ) - 2 * r := by
    rw [fullLineCenters_card_sub_emptyLineCenters_card_eq_cutDisplacement
      G hq hreg S htri, hdisplacement]
  have hemptyCard : (emptyLineCenters G S).card = r :=
    (full_empty_populations_of_saturated_deficit hsum hdiff).1
  rw [← hemptyCard]
  exact choose_two_le_secondOrderDefectPairs_of_clique_subset
    G (emptyLineCenters G S) C hemptyC hemptyClique

end

end Erdos85

#print axioms Erdos85.choose_two_le_secondOrderDefectPairs_of_clique_subset
#print axioms Erdos85.saturatedDeficit_choose_two_le_secondOrderDefectPairs
