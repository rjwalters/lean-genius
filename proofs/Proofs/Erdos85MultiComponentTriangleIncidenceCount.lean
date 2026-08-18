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

/-- Cyclic rotation preserves ordered multi-component ambient triangles. -/
theorem mem_multiComponentAmbientCyclicTriangles_rotate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (p : V × V × V) (hp : p ∈ multiComponentAmbientCyclicTriangles G) :
    (p.2.1, p.2.2, p.1) ∈ multiComponentAmbientCyclicTriangles G := by
  let D := secondOrderDefectGraph G
  simp only [multiComponentAmbientCyclicTriangles, Finset.mem_filter] at hp ⊢
  constructor
  · simp only [cyclicColoredTriples, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1.2.2, hp.1.1, hp.1.2.1⟩
  · rintro ⟨hyz, hyx⟩
    exact hp.2 ⟨hyx.symm, hyx.symm.trans hyz⟩

/-- The number of multi-component ambient triangles anchored in the first
coordinate equals the number anchored in the third coordinate. -/
theorem card_multiComponentAmbient_filter_first_eq_third
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card =
    ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.2 ∈ c.supp).card := by
  classical
  let M := multiComponentAmbientCyclicTriangles G
  apply Finset.card_bij (fun p _ => (p.2.1, p.2.2, p.1))
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨mem_multiComponentAmbientCyclicTriangles_rotate G p hp.1, hp.2⟩
  · intro p hp q hq heq
    rcases p with ⟨px, py, pz⟩
    rcases q with ⟨qx, qy, qz⟩
    simp only at heq
    cases heq
    rfl
  · intro q hq
    simp only [Finset.mem_filter] at hq
    let p : V × V × V := (q.2.2, q.1, q.2.1)
    have hpM : p ∈ M := by
      exact mem_multiComponentAmbientCyclicTriangles_rotate G
        (q.2.1, q.2.2, q.1)
        (mem_multiComponentAmbientCyclicTriangles_rotate G q hq.1)
    refine ⟨p, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hpM, hq.2⟩
    · simp [p]

/-- The number of multi-component ambient triangles anchored in the first
coordinate equals the number anchored in the second coordinate. -/
theorem card_multiComponentAmbient_filter_first_eq_second
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.1 ∈ c.supp).card =
    ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.1 ∈ c.supp).card := by
  classical
  let M := multiComponentAmbientCyclicTriangles G
  apply Finset.card_bij (fun p _ => (p.2.2, p.1, p.2.1))
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    have hpM := mem_multiComponentAmbientCyclicTriangles_rotate G p hp.1
    have hpM' := mem_multiComponentAmbientCyclicTriangles_rotate G
      (p.2.1, p.2.2, p.1) hpM
    exact ⟨hpM', hp.2⟩
  · intro p hp q hq heq
    rcases p with ⟨px, py, pz⟩
    rcases q with ⟨qx, qy, qz⟩
    simp only at heq
    cases heq
    rfl
  · intro q hq
    simp only [Finset.mem_filter] at hq
    let p : V × V × V := (q.2.1, q.2.2, q.1)
    have hpM : p ∈ M :=
      mem_multiComponentAmbientCyclicTriangles_rotate G q hq.1
    refine ⟨p, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hpM, hq.2⟩
    · simp [p]

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

/-- By cyclic symmetry, one anchored count of 96 suffices. -/
theorem multiComponentAmbientCyclicTriangles_card_eq_288_of_first_anchored_count
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
      fun p => p.1 ∈ c.supp).card = 96) :
    (multiComponentAmbientCyclicTriangles G).card = 288 := by
  have hsecond : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.1 ∈ c.supp).card = 96 := by
    rw [← card_multiComponentAmbient_filter_first_eq_second G c]
    exact hfirst
  have hthird : ((multiComponentAmbientCyclicTriangles G).filter
      fun p => p.2.2 ∈ c.supp).card = 96 := by
    rw [← card_multiComponentAmbient_filter_first_eq_third G c]
    exact hfirst
  exact multiComponentAmbientCyclicTriangles_card_eq_288_of_anchored_counts
    G c hexact hfirst hsecond hthird

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

/-- Final local interface: exact-one incidence and a single first-coordinate
anchored count of 96 imply the mu-three nonambient residue. -/
theorem orderSixtyFour_mixedNonambient_add_96_dvd_192_of_first_anchored_count
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
      fun p => p.1 ∈ c.supp).card = 96) :
    (192 : ℤ) ∣
      ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) + 96 := by
  apply orderSixtyFour_mixedNonambient_add_96_dvd_192_of_multiComponentAmbient_eq_288
    G hfree hreg hcard m hm hsum
  exact multiComponentAmbientCyclicTriangles_card_eq_288_of_first_anchored_count
    G c hexact hfirst

end

end Erdos85

#print axioms Erdos85.card_eq_add_three_filter_cards_of_exactlyOne
#print axioms
  Erdos85.multiComponentAmbientCyclicTriangles_card_eq_288_of_anchored_counts
#print axioms
  Erdos85.orderSixtyFour_mixedNonambient_add_96_dvd_192_of_anchored_counts
#print axioms Erdos85.mem_multiComponentAmbientCyclicTriangles_rotate
#print axioms Erdos85.card_multiComponentAmbient_filter_first_eq_second
#print axioms Erdos85.card_multiComponentAmbient_filter_first_eq_third
#print axioms
  Erdos85.multiComponentAmbientCyclicTriangles_card_eq_288_of_first_anchored_count
#print axioms
  Erdos85.orderSixtyFour_mixedNonambient_add_96_dvd_192_of_first_anchored_count
