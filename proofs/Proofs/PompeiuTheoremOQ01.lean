import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Pompeiu's theorem (pompeiu-theorem-oq-01)

Let `ABC` be an equilateral triangle (vertices modelled as complex numbers `a, b, c`) and let
`P` be an arbitrary point of the plane. Pompeiu's theorem states that the three distances
`PA, PB, PC` satisfy the triangle inequality, i.e. they are the side lengths of a (possibly
degenerate) triangle.

The proof rests on a single algebraic identity over `ℂ`:

    (P - A)(B - C) + (P - B)(C - A) + (P - C)(A - B) = 0.            (`pompeiu_identity`)

This is a `ring` fact for *any* four complex numbers. Taking norms, the three summands have
norms `PA·‖B-C‖`, `PB·‖C-A‖`, `PC·‖A-B‖`. Three complex numbers summing to zero have norms
satisfying the triangle inequality (`norm_le_of_add_eq_zero`), because each equals minus the
sum of the other two. For an *equilateral* triangle the three side lengths `‖A-B‖ = ‖B-C‖ =
‖C-A‖` coincide, so after cancelling the common positive side length we obtain the triangle
inequality on `PA, PB, PC` directly.

The whole argument is elementary and fully machine-checked: no axioms, no `sorry`.

Not a named Mathlib result.
-/

namespace PompeiuTheoremOQ01

open Complex

/-- **Pompeiu identity.** For *any* four complex numbers the three products vanish in sum.
This is the algebraic heart of Pompeiu's theorem. -/
theorem pompeiu_identity (a b c p : ℂ) :
    (p - a) * (b - c) + (p - b) * (c - a) + (p - c) * (a - b) = 0 := by
  ring

/-- If three complex numbers sum to zero, the norm of any one is at most the sum of the norms
of the other two (the triangle inequality for a closed vector triangle). -/
theorem norm_le_of_add_eq_zero {z₁ z₂ z₃ : ℂ} (h : z₁ + z₂ + z₃ = 0) :
    ‖z₁‖ ≤ ‖z₂‖ + ‖z₃‖ := by
  have hz : z₁ = -(z₂ + z₃) := by linear_combination h
  rw [hz, norm_neg]
  exact norm_add_le z₂ z₃

/-- **Pompeiu's theorem.** For an equilateral triangle `a, b, c` (all side lengths equal to the
common positive value `‖a - b‖ = ‖b - c‖ = ‖c - a‖`) and an arbitrary point `p`, the distances
`PA = ‖p - a‖`, `PB = ‖p - b‖`, `PC = ‖p - c‖` satisfy the triangle inequality `PA ≤ PB + PC`.
By symmetry the other two inequalities hold as well (see `pompeiu_triangle_inequalities`). -/
theorem pompeiu_dist_le
    (a b c p : ℂ)
    (hab : ‖a - b‖ = ‖b - c‖) (hbc : ‖b - c‖ = ‖c - a‖)
    (hpos : 0 < ‖b - c‖) :
    ‖p - a‖ ≤ ‖p - b‖ + ‖p - c‖ := by
  -- The three closed-triangle summands sum to zero (Pompeiu identity).
  have hkey := norm_le_of_add_eq_zero (pompeiu_identity a b c p)
  -- Rewrite each norm as distance · side length, using the equilateral hypotheses.
  rw [norm_mul, norm_mul, norm_mul] at hkey
  -- Express every side length as ‖b - c‖.
  have h1 : ‖b - c‖ = ‖b - c‖ := rfl
  have h2 : ‖c - a‖ = ‖b - c‖ := hbc.symm
  have h3 : ‖a - b‖ = ‖b - c‖ := hab.trans h1
  rw [h2, h3] at hkey
  -- hkey : ‖p - a‖ * ‖b - c‖ ≤ ‖p - b‖ * ‖b - c‖ + ‖p - c‖ * ‖b - c‖
  have hkey' : ‖p - a‖ * ‖b - c‖ ≤ (‖p - b‖ + ‖p - c‖) * ‖b - c‖ := by
    rw [add_mul]; exact hkey
  exact le_of_mul_le_mul_right hkey' hpos

/-- **Pompeiu's theorem (full statement).** For an equilateral triangle and an arbitrary point
`p`, the three distances `PA, PB, PC` satisfy all three triangle inequalities; hence they are
the side lengths of a (possibly degenerate) triangle. -/
theorem pompeiu_triangle_inequalities
    (a b c p : ℂ)
    (hab : ‖a - b‖ = ‖b - c‖) (hbc : ‖b - c‖ = ‖c - a‖)
    (hpos : 0 < ‖b - c‖) :
    ‖p - a‖ ≤ ‖p - b‖ + ‖p - c‖ ∧
    ‖p - b‖ ≤ ‖p - a‖ + ‖p - c‖ ∧
    ‖p - c‖ ≤ ‖p - a‖ + ‖p - b‖ := by
  -- The common side length and positivity, available in every cyclic relabelling.
  have hbc' : ‖b - c‖ = ‖c - a‖ := hbc
  have hca' : ‖c - a‖ = ‖a - b‖ := hbc.symm.trans hab.symm
  have hposca : 0 < ‖c - a‖ := hbc ▸ hpos
  have hposab : 0 < ‖a - b‖ := by rw [hab]; exact hpos
  refine ⟨pompeiu_dist_le a b c p hab hbc hpos, ?_, ?_⟩
  · -- PB ≤ PA + PC : relabel (a,b,c) → (b,c,a)
    have := pompeiu_dist_le b c a p hbc' hca' hposca
    -- this : ‖p - b‖ ≤ ‖p - c‖ + ‖p - a‖
    linarith [this]
  · -- PC ≤ PA + PB : relabel (a,b,c) → (c,a,b)
    have hca'' : ‖c - a‖ = ‖a - b‖ := hca'
    have hab'' : ‖a - b‖ = ‖b - c‖ := hab
    have := pompeiu_dist_le c a b p hca'' hab'' hposab
    -- this : ‖p - c‖ ≤ ‖p - a‖ + ‖p - b‖
    linarith [this]

end PompeiuTheoremOQ01
