import Mathlib
import Proofs.CarnotTheoremOQ01OQ03

/-
# Carnot's Theorem — the equilateral triangle is the *unique* maximiser of the sine sum

The companion file `CarnotTheoremOQ01OQ03.lean` proves the sharp bound

  `sin A + sin B + sin C ≤ 3√3 / 2`   (for `A + B + C = π`, `A, B, C ∈ [0, π]`),

with the equilateral triangle `A = B = C = π/3` attaining it. That file leaves the
maximiser's **uniqueness** open: is the equilateral triangle the *only* configuration
reaching `3√3 / 2`?

This file settles it: the bound is attained **iff** the triangle is equilateral,

  `sin A + sin B + sin C = 3√3 / 2  ↔  A = π/3 ∧ B = π/3 ∧ C = π/3`.

The upgrade from `≤` to a uniqueness `↔` is exactly where *strict* concavity of `sin`
on `[0, π]` does its work. The bound in the parent uses only ordinary concavity
(`strictConcaveOn_sin_Icc.concaveOn`), which can be tight even off the barycentre.
Strict concavity says the two-point Jensen inequality

  `a · sin x + b · sin y ≤ sin(a·x + b·y)`   (`a, b > 0`, `a + b = 1`)

is an *equality* only when `x = y`. The proof reaches the barycentre `π/3` in two
strict Jensen steps — first averaging `B, C` to their midpoint `M = (B + C)/2`, then
combining `A` (weight `1/3`) with `M` (weight `2/3`). Saturating the global bound
forces **both** steps to be tight, so:

* tightness of the first step gives `B = C`;
* tightness of the second gives `A = M = (B + C)/2 = C`.

Hence `A = B = C`, and `A + B + C = π` pins each to `π/3`. The converse is the
parent's evaluation `sin(π/3) + sin(π/3) + sin(π/3) = 3√3 / 2`.

This is the sharp-boundary refinement of the perimeter inequality: among all triangles
inscribed in a fixed circle, the equilateral one is the *unique* triangle of maximal
perimeter.

**No axioms, no sorries.**
-/

open Real

namespace CarnotTheoremOQ01OQ03OQ01

/-- **Strict two-point Jensen, equality case for `sin`.** If a strict two-point Jensen
inequality for `sin` on `[0, π]` is saturated (the chord meets the graph), the two
sample points coincide.

This is the contrapositive of strict concavity (`strictConcaveOn_sin_Icc.2`): for
`x ≠ y` and positive weights the inequality is *strict*, so equality forces `x = y`.
It is the single ingredient that turns the parent's maximum into a uniqueness
statement. -/
private lemma sin_jensen_eq_imp_eq {x y a b : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) π) (hy : y ∈ Set.Icc (0 : ℝ) π)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (heq : a * Real.sin x + b * Real.sin y = Real.sin (a * x + b * y)) : x = y := by
  by_contra hxy
  have hlt := strictConcaveOn_sin_Icc.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at hlt
  linarith [hlt, heq]

/-- **Uniqueness of the sine-sum maximiser.** For any reals with `A + B + C = π` and
`A, B, C ∈ [0, π]`, the sharp bound `sin A + sin B + sin C ≤ 3√3 / 2` is attained
*exactly* at the equilateral triangle:

  `sin A + sin B + sin C = 3√3 / 2  ↔  A = π/3 ∧ B = π/3 ∧ C = π/3`.

Forward: saturating the bound forces both strict Jensen steps (midpoint of `B, C`,
then `A` against that midpoint) to be equalities, giving `B = C` and `A = (B+C)/2`,
hence `A = B = C = π/3`. Backward: evaluate the sum at the equilateral angles, the
content of the parent's `sin_sum_eq_at_equilateral`. -/
theorem sin_sum_eq_iff_equilateral (A B C : ℝ)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (h : A + B + C = π) :
    Real.sin A + Real.sin B + Real.sin C = 3 * Real.sqrt 3 / 2
      ↔ A = π / 3 ∧ B = π / 3 ∧ C = π / 3 := by
  constructor
  · intro hsum
    set M : ℝ := (B + C) / 2 with hM
    have memA : A ∈ Set.Icc (0 : ℝ) π := ⟨hA0, by linarith⟩
    have memB : B ∈ Set.Icc (0 : ℝ) π := ⟨hB0, by linarith⟩
    have memC : C ∈ Set.Icc (0 : ℝ) π := ⟨hC0, by linarith⟩
    have memM : M ∈ Set.Icc (0 : ℝ) π := ⟨by rw [hM]; linarith, by rw [hM]; linarith⟩
    have hconc := strictConcaveOn_sin_Icc.concaveOn
    -- Step 1: ordinary Jensen at the midpoint of `B` and `C`.
    have step1 := hconc.2 memB memC (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    simp only [smul_eq_mul] at step1
    have eM : (1 / 2 : ℝ) * B + 1 / 2 * C = M := by rw [hM]; ring
    rw [eM] at step1
    -- Step 2: ordinary Jensen combining `A` (weight 1/3) with `M` (weight 2/3).
    have step2 := hconc.2 memA memM (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (1 / 3 : ℝ) + 2 / 3 = 1)
    simp only [smul_eq_mul] at step2
    have eP : (1 / 3 : ℝ) * A + 2 / 3 * M = π / 3 := by rw [hM]; linarith
    rw [eP, Real.sin_pi_div_three] at step2
    -- Saturating the global bound forces both Jensen steps to be tight.
    have ht1 : (1 / 2 : ℝ) * Real.sin B + 1 / 2 * Real.sin C = Real.sin M := by
      linarith [step1, step2, hsum]
    have ht2 : (1 / 3 : ℝ) * Real.sin A + 2 / 3 * Real.sin M = Real.sqrt 3 / 2 := by
      linarith [step1, step2, hsum]
    -- Tightness of step 1 ⟹ `B = C`; tightness of step 2 ⟹ `A = M`.
    have hBC : B = C := by
      apply sin_jensen_eq_imp_eq memB memC (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      rw [eM]; exact ht1
    have hAM : A = M := by
      apply sin_jensen_eq_imp_eq memA memM (by norm_num : (0 : ℝ) < 1 / 3)
        (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num : (1 / 3 : ℝ) + 2 / 3 = 1)
      rw [eP, Real.sin_pi_div_three]; exact ht2
    -- `A = M = (B + C)/2 = C` (using `B = C`), and `A + B + C = π` pins each to `π/3`.
    have hAeqC : A = C := by rw [hAM, hM, hBC]; ring
    refine ⟨?_, ?_, ?_⟩ <;> linarith [hAeqC, hBC, h]
  · rintro ⟨hA, hB, hC⟩
    rw [hA, hB, hC, Real.sin_pi_div_three]; ring

end CarnotTheoremOQ01OQ03OQ01
