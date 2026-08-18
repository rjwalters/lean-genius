import Proofs.Erdos85TwoMonochromaticFiveCapacity
import Proofs.Erdos85GridLargeBlockColorCapacity

/-!
# The all-TF `C10 + C6` fiber-margin obstruction

This is a finite, certificate-free consumer of the component overlap-load
equations.  Rows and columns `0,...,4` form the `C10`, while `5,6,7` form
the `C6`.
-/

namespace Erdos85

def tenSixHole (x y : Fin 8) : Prop :=
  if x.val < 5 then
    y.val = x.val ∨ y.val = (x.val + 4) % 5
  else
    y.val = x.val ∨ y.val = 5 + ((x.val - 5 + 2) % 3)

instance tenSixHole_decidable : DecidableRel tenSixHole := by
  intro x y
  unfold tenSixHole
  infer_instance

def tenSixRowOverlap (x h : Fin 8) : ℕ :=
  ((Finset.univ : Finset (Fin 8)).filter fun y =>
    tenSixHole x y ∧ tenSixHole h y).card

def tenSixColumnOverlap (y g : Fin 8) : ℕ :=
  ((Finset.univ : Finset (Fin 8)).filter fun x =>
    tenSixHole x y ∧ tenSixHole x g).card

theorem tenSixRowOverlap_five (x : Fin 8) :
    tenSixRowOverlap x 5 =
      if x = 5 then 2 else if x = 6 ∨ x = 7 then 1 else 0 := by
  fin_cases x <;> decide

theorem tenSixRowOverlap_six (x : Fin 8) :
    tenSixRowOverlap x 6 =
      if x = 6 then 2 else if x = 5 ∨ x = 7 then 1 else 0 := by
  fin_cases x <;> decide

theorem tenSixColumnOverlap_five (g : Fin 8) :
    tenSixColumnOverlap 5 g =
      if g = 5 then 2 else if g = 6 ∨ g = 7 then 1 else 0 := by
  fin_cases g <;> decide

theorem tenSixRowOverlap_of_right_small (x h : Fin 8) (hh : h.val < 5) :
    tenSixRowOverlap x h =
      if x = h then 2
      else if x.val < 5 ∧
        ((x.val + 1) % 5 = h.val ∨ (h.val + 1) % 5 = x.val)
      then 1 else 0 := by
  revert x h
  decide

theorem tenSixColumnOverlap_of_left_small (y g : Fin 8) (hy : y.val < 5) :
    tenSixColumnOverlap y g =
      if y = g then 2
      else if g.val < 5 ∧
        ((y.val + 1) % 5 = g.val ∨ (g.val + 1) % 5 = y.val)
      then 1 else 0 := by
  revert y g
  decide

def tenSixColorIndicator (color : Fin 8 → Fin 8 → Fin 3)
    (c : Fin 3) (x y : Fin 8) : ℕ :=
  if ¬ tenSixHole x y ∧ color x y = c then 1 else 0

def tenSixColumnMargin (color : Fin 8 → Fin 8 → Fin 3)
    (c : Fin 3) (h y : Fin 8) : Prop :=
  (∑ x : Fin 8,
      tenSixColorIndicator color c x y * tenSixRowOverlap x h) =
    ∑ g : Fin 8,
      tenSixColorIndicator color c h g * tenSixColumnOverlap y g

/-- The six-cycle part of the margin equations forces its three occupied
cells `(7,5)`, `(5,6)`, `(6,7)` to have one common color. -/
theorem tenSix_c6_occupied_colors_eq_of_columnMargins
    (color : Fin 8 → Fin 8 → Fin 3)
    (hmargin : ∀ c : Fin 3, ∀ h y : Fin 8,
      tenSixHole h y → tenSixColumnMargin color c h y) :
    color 7 5 = color 5 6 ∧ color 7 5 = color 6 7 := by
  have h₁ := hmargin (color 7 5) 5 5 (by decide)
  have h₂ := hmargin (color 7 5) 6 5 (by decide)
  norm_num [tenSixColumnMargin, tenSixColorIndicator,
    tenSixRowOverlap_five, tenSixRowOverlap_six,
    tenSixColumnOverlap_five, tenSixHole, Fin.sum_univ_succ] at h₁ h₂
  have hh₁ : color 5 6 = color 7 5 := by simpa using h₁
  have hh₂ : color 6 7 = color 7 5 := by simpa using h₂
  exact ⟨hh₁.symm, hh₂.symm⟩

/-- The five occupied cells immediately above the `C10` hole diagonal are
monochromatic. -/
theorem tenSix_c10_firstDiagonal_monochromatic_of_columnMargins
    (color : Fin 8 → Fin 8 → Fin 3)
    (hmargin : ∀ c : Fin 3, ∀ h y : Fin 8,
      tenSixHole h y → tenSixColumnMargin color c h y) :
    color 0 1 = color 1 2 ∧ color 0 1 = color 2 3 ∧
      color 0 1 = color 3 4 ∧ color 0 1 = color 4 0 := by
  let c := color 0 1
  have h0 := hmargin c 0 0 (by decide)
  have h4 := hmargin c 4 4 (by decide)
  have h3 := hmargin c 3 3 (by decide)
  have h2 := hmargin c 2 2 (by decide)
  have h1 := hmargin c 1 1 (by decide)
  norm_num [tenSixColumnMargin, tenSixColorIndicator,
    tenSixRowOverlap_of_right_small,
    tenSixColumnOverlap_of_left_small,
    tenSixHole, Fin.sum_univ_succ, c] at h0 h4 h3 h2 h1
  have e40 : color 4 0 = c := by simpa [c] using h0
  have e34 : color 3 4 = c := by simpa [c, e40] using h4
  have e23 : color 2 3 = c := by simpa [c, e34] using h3
  have e12 : color 1 2 = c := by simpa [c, e23] using h2
  exact ⟨e12.symm, e23.symm, e34.symm, e40.symm⟩

/-- The five occupied cells two steps below the `C10` hole diagonal are
monochromatic. -/
theorem tenSix_c10_secondDiagonal_monochromatic_of_columnMargins
    (color : Fin 8 → Fin 8 → Fin 3)
    (hmargin : ∀ c : Fin 3, ∀ h y : Fin 8,
      tenSixHole h y → tenSixColumnMargin color c h y) :
    color 2 0 = color 1 4 ∧ color 2 0 = color 0 3 ∧
      color 2 0 = color 4 2 ∧ color 2 0 = color 3 1 := by
  let c := color 2 0
  have h0 := hmargin c 1 0 (by decide)
  have h4 := hmargin c 0 4 (by decide)
  have h3 := hmargin c 4 3 (by decide)
  have h2 := hmargin c 3 2 (by decide)
  have h1 := hmargin c 2 1 (by decide)
  norm_num [tenSixColumnMargin, tenSixColorIndicator,
    tenSixRowOverlap_of_right_small,
    tenSixColumnOverlap_of_left_small,
    tenSixHole, Fin.sum_univ_succ, c] at h0 h4 h3 h2 h1
  have e14 : color 1 4 = c := by simpa [c] using h0
  have e03 : color 0 3 = c := by simpa [c, e14] using h4
  have e42 : color 4 2 = c := by simpa [c, e03] using h3
  have e31 : color 3 1 = c := by simpa [c, e42] using h2
  exact ⟨e14.symm, e03.symm, e42.symm, e31.symm⟩

def tenSixLargeBlock : Finset (Fin 8 × Fin 8) :=
  ((Finset.univ : Finset (Fin 8)).product Finset.univ).filter fun p =>
    p.1.val < 5 ∧ p.2.val < 5 ∧ ¬ tenSixHole p.1 p.2

def tenSixFirstDiagonal : Finset (Fin 8 × Fin 8) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)}

def tenSixSecondDiagonal : Finset (Fin 8 × Fin 8) :=
  {(2, 0), (1, 4), (0, 3), (4, 2), (3, 1)}

def tenSixColorFiber (color : Fin 8 → Fin 8 → Fin 3) (c : Fin 3) :
    Finset (Fin 8 × Fin 8) :=
  ((Finset.univ : Finset (Fin 8)).product Finset.univ).filter fun p =>
    ¬ tenSixHole p.1 p.2 ∧ color p.1 p.2 = c

def tenSixSmallRowStrip (color : Fin 8 → Fin 8 → Fin 3) (c : Fin 3) :
    Finset (Fin 8 × Fin 8) :=
  (tenSixColorFiber color c).filter fun p => 5 ≤ p.1.val

def tenSixSmallColumnStrip (color : Fin 8 → Fin 8 → Fin 3) (c : Fin 3) :
    Finset (Fin 8 × Fin 8) :=
  (tenSixColorFiber color c).filter fun p => 5 ≤ p.2.val

def tenSixC6Occupied : Finset (Fin 8 × Fin 8) :=
  {(7, 5), (5, 6), (6, 7)}

set_option maxHeartbeats 800000 in
/-- Exact fiber and small-strip counts turn the C6 monochromaticity into the
`7,4,4` C10-block capacities. -/
theorem tenSix_largeBlock_color_card_eq_of_fiberStripCounts
    (color : Fin 8 → Fin 8 → Fin 3)
    (hC6 : color 7 5 = color 5 6 ∧ color 7 5 = color 6 7)
    (hfiber : ∀ c : Fin 3, (tenSixColorFiber color c).card = 16)
    (hrow : ∀ c : Fin 3, (tenSixSmallRowStrip color c).card = 6)
    (hcolumn : ∀ c : Fin 3,
      (tenSixSmallColumnStrip color c).card = 6) (c : Fin 3) :
    (tenSixLargeBlock.filter fun p => color p.1 p.2 = c).card =
      if c = color 7 5 then 7 else 4 := by
  classical
  let F := tenSixColorFiber color c
  let R := tenSixSmallRowStrip color c
  let Q := tenSixSmallColumnStrip color c
  have hRsub : R ⊆ F := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hQsub : Q ⊆ F := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hinterSet : R ∩ Q =
      if c = color 7 5 then tenSixC6Occupied else ∅ := by
    by_cases hc : c = color 7 5
    · have hc56 : c = color 5 6 := hc.trans hC6.1
      have hc67 : c = color 6 7 := hc.trans hC6.2
      ext p
      rcases p with ⟨x, y⟩
      fin_cases x <;> fin_cases y <;>
        simp [R, Q, tenSixSmallRowStrip, tenSixSmallColumnStrip,
          tenSixColorFiber, tenSixC6Occupied, tenSixHole, hc, hc56, hc67,
          hC6.1.symm, hC6.2.symm]
    · have hc56 : c ≠ color 5 6 := by
        intro heq
        exact hc (heq.trans hC6.1.symm)
      have hc67 : c ≠ color 6 7 := by
        intro heq
        exact hc (heq.trans hC6.2.symm)
      have h56c : color 5 6 ≠ c := Ne.symm hc56
      have h67c : color 6 7 ≠ c := Ne.symm hc67
      have h75c : color 7 5 ≠ c := Ne.symm hc
      ext p
      rcases p with ⟨x, y⟩
      fin_cases x <;> fin_cases y <;>
        simp [R, Q, tenSixSmallRowStrip, tenSixSmallColumnStrip,
          tenSixColorFiber, tenSixC6Occupied, tenSixHole, hc, hc56, hc67,
          h56c, h67c, h75c]
  have hinter : (R ∩ Q).card = if c = color 7 5 then 3 else 0 := by
    rw [hinterSet]
    split <;> simp [tenSixC6Occupied]
  have hblock : F \ (R ∪ Q) =
      tenSixLargeBlock.filter fun p => color p.1 p.2 = c := by
    ext p
    rcases p with ⟨x, y⟩
    simp only [F, R, Q, tenSixColorFiber, tenSixSmallRowStrip,
      tenSixSmallColumnStrip, tenSixLargeBlock, Finset.mem_sdiff,
      Finset.mem_union, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hp, hK, hcolor⟩, hout⟩
      have hx : x.val < 5 := by
        by_contra hn
        push_neg at hn
        exact hout (Or.inl ⟨⟨hp, hK, hcolor⟩, hn⟩)
      have hy : y.val < 5 := by
        by_contra hn
        push_neg at hn
        exact hout (Or.inr ⟨⟨hp, hK, hcolor⟩, hn⟩)
      exact ⟨⟨hp, hx, hy, hK⟩, hcolor⟩
    · rintro ⟨⟨hp, hx, hy, hK⟩, hcolor⟩
      refine ⟨⟨hp, hK, hcolor⟩, ?_⟩
      rintro (hR | hQ)
      · exact (by omega : ¬ 5 ≤ x.val) hR.2
      · exact (by omega : ¬ 5 ≤ y.val) hQ.2
  rw [← hblock]
  exact largeBlockColor_card_eq_of_two_strips F R Q (c = color 7 5)
    (hfiber c) (hrow c) (hcolumn c) hRsub hQsub hinter

/-- Margins plus the `7,4,4` C10-block capacities are inconsistent. -/
theorem false_of_tenSix_columnMargins_of_largeBlock_capacities
    (color : Fin 8 → Fin 8 → Fin 3)
    (hmargin : ∀ c : Fin 3, ∀ h y : Fin 8,
      tenSixHole h y → tenSixColumnMargin color c h y)
    (hcap : ∀ c : Fin 3,
      (tenSixLargeBlock.filter fun p => color p.1 p.2 = c).card ≤
        if c = color 7 5 then 7 else 4) : False := by
  have hD₁ := tenSix_c10_firstDiagonal_monochromatic_of_columnMargins
    color hmargin
  have hD₂ := tenSix_c10_secondDiagonal_monochromatic_of_columnMargins
    color hmargin
  apply false_of_two_disjoint_monochromatic_five_in_of_capacities
    (fun p : Fin 8 × Fin 8 => color p.1 p.2) (color 7 5)
    tenSixLargeBlock tenSixFirstDiagonal tenSixSecondDiagonal
    (color 0 1) (color 2 0)
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro p hp
    simp only [tenSixFirstDiagonal, Finset.mem_insert,
      Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact hD₁.1.symm
    · exact hD₁.2.1.symm
    · exact hD₁.2.2.1.symm
    · exact hD₁.2.2.2.symm
  · intro p hp
    simp only [tenSixSecondDiagonal, Finset.mem_insert,
      Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact hD₂.1.symm
    · exact hD₂.2.1.symm
    · exact hD₂.2.2.1.symm
    · exact hD₂.2.2.2.symm
  · exact hcap

/-- Complete certificate-free contradiction from column margins and the
exact component fiber/strip counts. -/
theorem false_of_tenSix_columnMargins_of_fiberStripCounts
    (color : Fin 8 → Fin 8 → Fin 3)
    (hmargin : ∀ c : Fin 3, ∀ h y : Fin 8,
      tenSixHole h y → tenSixColumnMargin color c h y)
    (hfiber : ∀ c : Fin 3, (tenSixColorFiber color c).card = 16)
    (hrow : ∀ c : Fin 3, (tenSixSmallRowStrip color c).card = 6)
    (hcolumn : ∀ c : Fin 3,
      (tenSixSmallColumnStrip color c).card = 6) : False := by
  have hC6 := tenSix_c6_occupied_colors_eq_of_columnMargins color hmargin
  apply false_of_tenSix_columnMargins_of_largeBlock_capacities color hmargin
  intro c
  rw [tenSix_largeBlock_color_card_eq_of_fiberStripCounts
    color hC6 hfiber hrow hcolumn c]

end Erdos85

#print axioms Erdos85.tenSix_c6_occupied_colors_eq_of_columnMargins
#print axioms Erdos85.tenSix_c10_firstDiagonal_monochromatic_of_columnMargins
#print axioms Erdos85.tenSix_c10_secondDiagonal_monochromatic_of_columnMargins
#print axioms Erdos85.tenSix_largeBlock_color_card_eq_of_fiberStripCounts
#print axioms Erdos85.false_of_tenSix_columnMargins_of_largeBlock_capacities
#print axioms Erdos85.false_of_tenSix_columnMargins_of_fiberStripCounts
