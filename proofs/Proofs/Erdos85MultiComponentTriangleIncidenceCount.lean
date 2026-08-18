import Proofs.Erdos85OrderSixtyFourMuThreeMixedTriangleResidue

/-!
# Incidence counting for multi-component ambient triangles

This converts local anchored triangle counts into the global ordered count
used by the mixed-owner residue.  The only structural input is that each
multi-component triangle contains exactly one vertex of the distinguished
defect component.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A finite set partitioned by three mutually exclusive predicates has card
equal to the sum of the three filter cards. -/
theorem card_eq_add_three_filter_cards_of_exactlyOne
    {α : Type*} [DecidableEq α] (s : Finset α)
    (P Q R : α → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hexact : ∀ x ∈ s,
      (P x ∧ ¬ Q x ∧ ¬ R x) ∨
      (¬ P x ∧ Q x ∧ ¬ R x) ∨
      (¬ P x ∧ ¬ Q x ∧ R x)) :
    s.card = (s.filter P).card + (s.filter Q).card + (s.filter R).card := by
  classical
  calc
    s.card = ∑ x ∈ s, 1 := by simp
    _ = ∑ x ∈ s,
        ((if P x then 1 else 0) + (if Q x then 1 else 0) +
          (if R x then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rcases hexact x hx with h | h | h <;> simp [h.1, h.2.1, h.2.2]
    _ = (s.filter P).card + (s.filter Q).card + (s.filter R).card := by
      simp only [Finset.sum_add_distrib]
      congr <;> simp

/-- If every multi-component ambient triangle meets component `c` in exactly
one vertex and each of the three ordered coordinate positions contributes 96
triangles, then the global ordered multi-component count is 288. -/
theorem multiComponentAmbientCyclicTriangles_card_eq_288_of_anchored_counts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hexact : ∀ p ∈ multiComponentAmbientCyclicTriangles G,
      (p.1 ∈ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∈ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∈ c.supp))
    (hfirst : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card = 96)
    (hsecond : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.1 ∈ c.supp).card = 96)
    (hthird : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.2 ∈ c.supp).card = 96) :
    (multiComponentAmbientCyclicTriangles G).card = 288 := by
  have hpartition := card_eq_add_three_filter_cards_of_exactlyOne
    (multiComponentAmbientCyclicTriangles G)
    (fun p => p.1 ∈ c.supp) (fun p => p.2.1 ∈ c.supp)
    (fun p => p.2.2 ∈ c.supp) hexact
  omega

/-- Local-incidence version of the mu-three residue consumer. -/
theorem orderSixtyFour_mixedNonambient_add_96_dvd_192_of_anchored_counts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (hsum : ∑ c, m c = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hexact : ∀ p ∈ multiComponentAmbientCyclicTriangles G,
      (p.1 ∈ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∈ c.supp ∧ p.2.2 ∉ c.supp) ∨
      (p.1 ∉ c.supp ∧ p.2.1 ∉ c.supp ∧ p.2.2 ∈ c.supp))
    (hfirst : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card = 96)
    (hsecond : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.1 ∈ c.supp).card = 96)
    (hthird : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.2 ∈ c.supp).card = 96) :
    (192 : ℤ) ∣
      ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) + 96 := by
  apply orderSixtyFour_mixedNonambient_add_96_dvd_192_of_multiComponentAmbient_eq_288
    G hfree hreg hcard m hm hsum
  exact multiComponentAmbientCyclicTriangles_card_eq_288_of_anchored_counts
    G c hexact hfirst hsecond hthird

end

end Erdos85

#print axioms Erdos85.card_eq_add_three_filter_cards_of_exactlyOne
#print axioms
  Erdos85.multiComponentAmbientCyclicTriangles_card_eq_288_of_anchored_counts
#print axioms
  Erdos85.orderSixtyFour_mixedNonambient_add_96_dvd_192_of_anchored_counts
