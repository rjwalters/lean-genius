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

/-- Splitting a defect clique across an arbitrary shore retains the exact
sum of the two within-shore pair penalties. -/
theorem splitClique_choose_two_le_secondOrderDefectPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (E B : Finset V)
    (hclique : ∀ ⦃u v⦄, u ∈ E → v ∈ E → u ≠ v →
      (secondOrderDefectGraph G).Adj u v) :
    (E ∩ B).card.choose 2 + (E ∩ Bᶜ).card.choose 2 ≤
      (secondOrderDefectPairs G B).card +
        (secondOrderDefectPairs G Bᶜ).card := by
  have hleft := choose_two_le_secondOrderDefectPairs_of_clique_subset
    G (E ∩ B) B Finset.inter_subset_right
    (by
      intro u v hu hv huv
      exact hclique (Finset.mem_inter.mp hu).1
        (Finset.mem_inter.mp hv).1 huv)
  have hright := choose_two_le_secondOrderDefectPairs_of_clique_subset
    G (E ∩ Bᶜ) Bᶜ Finset.inter_subset_right
    (by
      intro u v hu hv huv
      exact hclique (Finset.mem_inter.mp hu).1
        (Finset.mem_inter.mp hv).1 huv)
  omega

/-- Division-free convexity bound for the two pieces of an `r`-set. -/
theorem split_choose_two_quadratic_lower
    {a b r : ℕ} (hsum : a + b = r) :
    r * r ≤ 4 * (a.choose 2 + b.choose 2) + 2 * r := by
  have haEven : Even (a * (a - 1)) := Nat.even_mul_pred_self a
  have hbEven : Even (b * (b - 1)) := Nat.even_mul_pred_self b
  have ha : 2 * a.choose 2 = a * (a - 1) := by
    rw [Nat.choose_two_right, Nat.mul_comm]
    exact Nat.div_two_mul_two_of_even haEven
  have hb : 2 * b.choose 2 = b * (b - 1) := by
    rw [Nat.choose_two_right, Nat.mul_comm]
    exact Nat.div_two_mul_two_of_even hbEven
  have haProd : a * (a - 1) + a = a * a := by
    by_cases ha0 : a = 0
    · simp [ha0]
    · calc
        a * (a - 1) + a = a * ((a - 1) + 1) := by ring
        _ = a * a := by
          rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ha0)]
  have hbProd : b * (b - 1) + b = b * b := by
    by_cases hb0 : b = 0
    · simp [hb0]
    · calc
        b * (b - 1) + b = b * ((b - 1) + 1) := by ring
        _ = b * b := by
          rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hb0)]
  nlinarith [two_mul_le_add_sq a b]

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

/-- No containment choice is needed: the canonical empty clique splits
across `B` and its complement, its two populations add to `r`, and their
within-shore pairs contribute to the corresponding defect-pair penalties. -/
theorem saturatedDeficit_splitMinority_defectPairPenalty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {q r : ℕ} (hq : 0 < q) (hreg : ∀ x, G.degree x = q)
    (S B : Finset V)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hsupportCard : (exceptionalSignedSupport G S q).card = q)
    (hdisplacement :
      2 * (S.card : ℤ) - Fintype.card V = (q : ℤ) - 2 * r) :
    (emptyLineCenters G S ∩ B).card +
          (emptyLineCenters G S ∩ Bᶜ).card = r ∧
      (emptyLineCenters G S ∩ B).card.choose 2 +
          (emptyLineCenters G S ∩ Bᶜ).card.choose 2 ≤
        (secondOrderDefectPairs G B).card +
          (secondOrderDefectPairs G Bᶜ).card := by
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
  constructor
  · classical
    have hunion :
        (emptyLineCenters G S ∩ B) ∪ (emptyLineCenters G S ∩ Bᶜ) =
          emptyLineCenters G S := by
      ext x
      by_cases hx : x ∈ B <;> simp [hx]
    have hdisj : Disjoint (emptyLineCenters G S ∩ B)
        (emptyLineCenters G S ∩ Bᶜ) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp hy).2)
        (Finset.mem_inter.mp hx).2
    calc
      (emptyLineCenters G S ∩ B).card +
          (emptyLineCenters G S ∩ Bᶜ).card =
          ((emptyLineCenters G S ∩ B) ∪
            (emptyLineCenters G S ∩ Bᶜ)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
      _ = (emptyLineCenters G S).card := congrArg Finset.card hunion
      _ = r := hemptyCard
  · exact splitClique_choose_two_le_secondOrderDefectPairs
      G (emptyLineCenters G S) B hemptyClique

/-- Location-free quadratic form of the split-minority penalty. -/
theorem saturatedDeficit_splitMinority_quadratic_defectPairPenalty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {q r : ℕ} (hq : 0 < q) (hreg : ∀ x, G.degree x = q)
    (S B : Finset V)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hsupportCard : (exceptionalSignedSupport G S q).card = q)
    (hdisplacement :
      2 * (S.card : ℤ) - Fintype.card V = (q : ℤ) - 2 * r) :
    r * r ≤
      4 * ((secondOrderDefectPairs G B).card +
        (secondOrderDefectPairs G Bᶜ).card) + 2 * r := by
  have hsplit := saturatedDeficit_splitMinority_defectPairPenalty
    G hq hreg S B htri hemptyClique hsupportCard hdisplacement
  have hquad := split_choose_two_quadratic_lower hsplit.1
  omega

end

end Erdos85

#print axioms Erdos85.choose_two_le_secondOrderDefectPairs_of_clique_subset
#print axioms Erdos85.splitClique_choose_two_le_secondOrderDefectPairs
#print axioms Erdos85.split_choose_two_quadratic_lower
#print axioms Erdos85.saturatedDeficit_choose_two_le_secondOrderDefectPairs
#print axioms Erdos85.saturatedDeficit_splitMinority_defectPairPenalty
#print axioms Erdos85.saturatedDeficit_splitMinority_quadratic_defectPairPenalty
