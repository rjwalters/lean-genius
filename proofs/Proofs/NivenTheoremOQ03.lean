import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Niven
import Mathlib.Tactic

/-
# Niven's Theorem for Tangent

## What This Proves
If `θ` is a rational multiple of `π` (i.e. `θ = (m/n)·π`) and `tan θ` is rational,
then `tan θ ∈ {0, 1, -1}`.

This is the tangent companion to Niven's theorem. The gallery entries prove the
*cosine* case (`niven-theorem-oq-01`, `Proofs/NivenTheorem.lean`) and the *sine*
case (`niven-theorem-oq-02`, `Proofs/NivenTheoremOQ02.lean`). The set of admissible
rational values shrinks from the five `{0, ±1/2, ±1}` for sine/cosine to just the
three `{0, ±1}` for tangent.

## Approach
The result reduces to cosine Niven via the double-angle identity
`cos (2θ) = (1 - tan²θ) / (1 + tan²θ)`, valid whenever `cos θ ≠ 0`.

* If `cos θ = 0` then (by Lean's `Real.tan = sin / cos` convention) `tan θ = 0`,
  which is already in the target set.
* Otherwise put `t := tan θ` (rational by hypothesis). Then `2θ` is again a
  rational multiple of `π` and `cos (2θ) = (1 - t²)/(1 + t²)` is rational, so
  cosine Niven pins `cos (2θ) ∈ {0, ±1/2, ±1}`. Solving `(1 - t²)/(1 + t²) = v`
  for each value:
  - `v = 1`   ⟹ `t² = 0` ⟹ `t = 0`;
  - `v = 0`   ⟹ `t² = 1` ⟹ `t = ±1`;
  - `v = -1`  is impossible (`1 = -1`);
  - `v = 1/2` ⟹ `t² = 1/3`, impossible for rational `t`;
  - `v = -1/2`⟹ `t² = 3`,   impossible for rational `t`.

  The two `±1/2` branches are excluded because no rational number squares to `3`
  (equivalently `√3` is irrational), which kills both `t² = 3` and `t² = 1/3`
  (rescale by `3`).

## Status
- [x] Cosine core restated (delegates the algebraic-integer step to Mathlib's
      `Real.isIntegral_two_mul_cos_rat_mul_pi`, as in `niven-theorem-oq-01/02`)
- [x] Tangent corollary derived via the double-angle identity + `√3 ∉ ℚ`

## Mathlib Dependencies
- `Real.isIntegral_two_mul_cos_rat_mul_pi` — `2 cos(q π)` is integral over `ℤ`
- `Real.cos_two_mul`, `Real.sin_sq_add_cos_sq`, `Real.tan_eq_sin_div_cos`
- `Nat.Prime.irrational_sqrt` + `Nat.prime_three` — irrationality of `√3`
- `Real.sqrt_sq_eq_abs`, `Rat.cast_abs`, `Rat.not_irrational`
-/

namespace NivenTheoremOQ03

open Real

/-- **Cosine Niven (helper).** Restated from `niven-theorem-oq-01` so the tangent
corollary is self-contained: if `θ` is a rational multiple of `π` and `cos θ` is
rational, then `cos θ ∈ {0, ±1/2, ±1}`. The deep step (`2 cos θ` is an algebraic
integer) is delegated to Mathlib. -/
theorem cos_niven (θ : ℝ) (m n : ℤ) (hn : n ≠ 0) (hθ : θ = (m / n : ℝ) * π)
    (hcos : ∃ r : ℚ, Real.cos θ = r) :
    Real.cos θ = 0 ∨ Real.cos θ = 1 / 2 ∨ Real.cos θ = -1 / 2 ∨
      Real.cos θ = 1 ∨ Real.cos θ = -1 := by
  obtain ⟨r, hr⟩ := hcos
  have hq : θ = ((m / n : ℚ) : ℝ) * π := by rw [hθ]; push_cast; ring
  have hint : IsIntegral ℤ (2 * Real.cos θ) := by
    rw [hq]; exact Real.isIntegral_two_mul_cos_rat_mul_pi (m / n)
  obtain ⟨k, hk⟩ :=
    hint.exists_int_iff_exists_rat.mp ⟨2 * r, by rw [hr]; push_cast; ring⟩
  have hub : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hlb : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hkl : -2 ≤ k := by
    have : (-2 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have hku : k ≤ 2 := by
    have : (k : ℝ) ≤ 2 := by linarith
    exact_mod_cast this
  interval_cases k <;> push_cast at hk
  · right; right; right; right; linarith
  · right; right; left; linarith
  · left; linarith
  · right; left; linarith
  · right; right; right; left; linarith

/-- No rational number squares to `3`: `(s : ℝ)² ≠ 3` for every `s : ℚ`.
This is the arithmetic obstruction that rules out `tan θ = ±1/√3, ±√3`. -/
theorem no_rat_sq_eq_three (s : ℚ) : (s : ℝ) ^ 2 ≠ 3 := by
  intro h
  have hsqrt : Real.sqrt 3 = |(s : ℝ)| := by rw [← h, Real.sqrt_sq_eq_abs]
  have hirr : Irrational (Real.sqrt 3) := by
    simpa using (Nat.prime_three.irrational_sqrt)
  exact hirr ⟨|s|, by rw [Rat.cast_abs]; exact hsqrt.symm⟩

/-- **Niven's Theorem for tangent.** If `θ` is a rational multiple of `π` and
`tan θ` is rational, then `tan θ ∈ {0, 1, -1}`. -/
theorem tan_niven (θ : ℝ) (m n : ℤ) (hn : n ≠ 0) (hθ : θ = (m / n : ℝ) * π)
    (htan : ∃ r : ℚ, Real.tan θ = r) :
    Real.tan θ = 0 ∨ Real.tan θ = 1 ∨ Real.tan θ = -1 := by
  by_cases hc : Real.cos θ = 0
  · -- `tan θ = sin θ / cos θ = sin θ / 0 = 0` by Lean's division convention.
    left
    rw [Real.tan_eq_sin_div_cos, hc, div_zero]
  · obtain ⟨t, ht⟩ := htan
    have hpos : (0 : ℝ) < 1 + (t : ℝ) ^ 2 := by positivity
    -- Double-angle identity in terms of the tangent value `t`.
    have key : Real.cos (2 * θ) = (1 - (t : ℝ) ^ 2) / (1 + (t : ℝ) ^ 2) := by
      rw [eq_div_iff hpos.ne', Real.cos_two_mul, ← ht, Real.tan_eq_sin_div_cos]
      have hpyth := Real.sin_sq_add_cos_sq θ
      field_simp
      nlinarith [hpyth]
    -- `cos (2θ)` is rational, and `2θ` is a rational multiple of `π`.
    have hcosrat : ∃ r : ℚ, Real.cos (2 * θ) = r :=
      ⟨(1 - t ^ 2) / (1 + t ^ 2), by rw [key]; push_cast; ring⟩
    have hθ2 : 2 * θ = ((2 * m : ℤ) : ℝ) / ((n : ℤ) : ℝ) * π := by
      rw [hθ]; push_cast; ring
    have hcn := cos_niven (2 * θ) (2 * m) n hn hθ2 hcosrat
    rw [ht]
    rw [key] at hcn
    rcases hcn with h0 | hhalf | hneghalf | h1 | hneg1
    · -- `cos 2θ = 0` ⟹ `t² = 1` ⟹ `t = ±1`.
      rw [div_eq_zero_iff] at h0
      have hnum : (1 : ℝ) - (t : ℝ) ^ 2 = 0 := h0.resolve_right hpos.ne'
      have hfac : ((t : ℝ) - 1) * ((t : ℝ) + 1) = 0 := by nlinarith [hnum]
      rcases mul_eq_zero.mp hfac with h | h
      · right; left; linarith
      · right; right; linarith
    · -- `cos 2θ = 1/2` ⟹ `t² = 1/3` ⟹ `(3t)² = 3`, impossible.
      rw [div_eq_iff hpos.ne'] at hhalf
      have hsq : ((3 * t : ℚ) : ℝ) ^ 2 = 3 := by push_cast; nlinarith [hhalf]
      exact absurd hsq (no_rat_sq_eq_three (3 * t))
    · -- `cos 2θ = -1/2` ⟹ `t² = 3`, impossible.
      rw [div_eq_iff hpos.ne'] at hneghalf
      have hsq : ((t : ℚ) : ℝ) ^ 2 = 3 := by nlinarith [hneghalf]
      exact absurd hsq (no_rat_sq_eq_three t)
    · -- `cos 2θ = 1` ⟹ `t² = 0` ⟹ `t = 0`.
      rw [div_eq_iff hpos.ne'] at h1
      have hzero : (t : ℝ) ^ 2 = 0 := by nlinarith [h1]
      left
      exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hzero
    · -- `cos 2θ = -1` is impossible: it forces `1 = -1`.
      rw [div_eq_iff hpos.ne'] at hneg1
      exfalso; nlinarith [hneg1]

end NivenTheoremOQ03
