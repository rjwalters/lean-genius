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

end Erdos85

#print axioms Erdos85.tenSix_c6_occupied_colors_eq_of_columnMargins
#print axioms Erdos85.tenSix_c10_firstDiagonal_monochromatic_of_columnMargins
#print axioms Erdos85.tenSix_c10_secondDiagonal_monochromatic_of_columnMargins
