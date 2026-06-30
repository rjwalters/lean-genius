import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Niven
import Mathlib.Tactic

/-
# Niven's Theorem for Sine at the special angles `2π/n`

## What This Proves
For every positive integer `n`,

    `sin (2π/n)` is rational  ⟺  `n ∈ {1, 2, 4, 12}`,

with the explicit values

    n:    1     2     4     12
    sin:  0     0     1     1/2

This is the *sine* companion of the crystallographic-restriction classification
`cos(2π/n)` rational ⟺ `n ∈ {1, 2, 3, 4, 6}` (gallery entry
`nth-root-irrational-oq-01-oq-01`, file `NthRootIrrationalOQ01OQ01CosRational.lean`).
The exceptional set is *different* — `{1,2,4,12}` versus `{1,2,3,4,6}` — because the
fixed numerator `2` interacts with the period of `sin` differently from that of
`cos`.

## Approach
The forward direction combines two ingredients:

1. **Niven's restriction for sine** (`sin_niven`, restated here so the file is
   self-contained): if `θ` is a rational multiple of `π` and `sin θ` is rational,
   then `sin θ ∈ {0, ±1/2, ±1}`. We delegate the deep algebraic-integer step to
   Mathlib's `Real.isIntegral_two_mul_cos_rat_mul_pi` and pass to sine through the
   co-function identity `cos (π/2 − θ) = sin θ`, exactly as the gallery's
   `niven-theorem-oq-02`.

2. **Injectivity of `sin` on `[-π/2, π/2]`** (`Real.strictMonoOn_sin.injOn`):
   for `n ≥ 4` the angle `2π/n` lies in `(0, π/2]`, where `sin` is strictly
   increasing. Positivity of `sin` on `(0, π)` discards the values `0, −1/2, −1`,
   leaving `sin(2π/n) ∈ {1/2, 1}`; injectivity then pins `2π/n = π/6` (so `n = 12`)
   or `2π/n = π/2` (so `n = 4`).

   The small cases `n = 1, 2` give `sin = 0` (rational); `n = 3` gives
   `sin(2π/3) = √3/2`, which is irrational (the arithmetic obstruction
   `(s:ℝ)² ≠ 3`), so `3` is correctly excluded.

The reverse direction is five elementary special-angle evaluations.

## Mathlib Dependencies
- `Real.isIntegral_two_mul_cos_rat_mul_pi`, `IsIntegral.exists_int_iff_exists_rat`
  — Niven's algebraic-integer core (via the cosine helper).
- `Real.cos_pi_div_two_sub` — co-function identity to pass cosine ⟶ sine.
- `Real.strictMonoOn_sin` — `sin` strictly increasing on `[-π/2, π/2]`.
- `Real.sin_pos_of_pos_of_lt_pi` — positivity of `sin` on `(0, π)`.
- `Real.sin_two_pi`, `Real.sin_pi`, `Real.sin_pi_div_two`, `Real.sin_pi_div_six`,
  `Real.sin_pi_div_three`, `Real.sin_pi_sub` — special-angle values.
- `Nat.prime_three.irrational_sqrt` — `√3` is irrational.

0 axioms, 0 sorries.
-/

namespace NivenTheoremOQ01OQ03

open Real

/-- **Cosine Niven (helper).** If `θ` is a rational multiple of `π` and `cos θ` is
rational, then `cos θ ∈ {0, ±1/2, ±1}`. The deep step (`2 cos θ` is an algebraic
integer) is delegated to Mathlib. Restated from `niven-theorem-oq-01` so this file
is self-contained. -/
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

/-- **Niven's Theorem for sine (helper).** If `θ` is a rational multiple of `π` and
`sin θ` is rational, then `sin θ ∈ {0, ±1/2, ±1}`. Derived from `cos_niven` via the
co-function identity `cos (π/2 − θ) = sin θ`. -/
theorem sin_niven (θ : ℝ) (m n : ℤ) (hn : n ≠ 0) (hθ : θ = (m / n : ℝ) * π)
    (hsin : ∃ r : ℚ, Real.sin θ = r) :
    Real.sin θ = 0 ∨ Real.sin θ = 1 / 2 ∨ Real.sin θ = -1 / 2 ∨
      Real.sin θ = 1 ∨ Real.sin θ = -1 := by
  set φ := π / 2 - θ with hφ
  have hsc : Real.cos φ = Real.sin θ := by rw [hφ, Real.cos_pi_div_two_sub]
  have hφeq : φ = ((↑(n - 2 * m) : ℝ) / (↑(2 * n) : ℝ)) * π := by
    rw [hφ, hθ]
    push_cast
    field_simp
  have h2n : (2 * n : ℤ) ≠ 0 := mul_ne_zero (by norm_num) hn
  have hcosrat : ∃ r : ℚ, Real.cos φ = r := by
    obtain ⟨r, hr⟩ := hsin
    exact ⟨r, by rw [hsc, hr]⟩
  have hcn := cos_niven φ (n - 2 * m) (2 * n) h2n hφeq hcosrat
  rwa [hsc] at hcn

/-- No rational number squares to `3`. Arithmetic obstruction ruling out
`sin(2π/3) = √3/2 ∈ ℚ`. -/
private theorem no_rat_sq_eq_three (s : ℚ) : (s : ℝ) ^ 2 ≠ 3 := by
  intro h
  have hsqrt : Real.sqrt 3 = |(s : ℝ)| := by rw [← h, Real.sqrt_sq_eq_abs]
  have hirr : Irrational (Real.sqrt 3) := by simpa using (Nat.prime_three.irrational_sqrt)
  exact hirr ⟨|s|, by rw [Rat.cast_abs]; exact hsqrt.symm⟩

/-- `sin(2π/3) = √3/2` is irrational; this is why `n = 3` is excluded from the
classification (it *is* in the cosine exceptional set `{1,2,3,4,6}`). -/
theorem sin_two_pi_div_three_irrational : ¬ ∃ r : ℚ, Real.sin (2 * π / 3) = r := by
  rintro ⟨r, hr⟩
  have he : (2 * π / 3) = π - π / 3 := by ring
  rw [he, Real.sin_pi_sub, Real.sin_pi_div_three] at hr
  -- hr : √3 / 2 = ↑r
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hval : (2 : ℝ) * (r : ℝ) = Real.sqrt 3 := by rw [← hr]; ring
  exact no_rat_sq_eq_three (2 * r) (by push_cast; rw [hval]; exact h3)

/-- **Sine crystallographic-restriction classification.** For a positive integer
`n`, the value `sin(2π/n)` is rational iff `n ∈ {1, 2, 4, 12}`. -/
theorem sin_two_pi_div_rational_iff {n : ℕ} (hn : 1 ≤ n) :
    (∃ r : ℚ, Real.sin (2 * π / n) = r) ↔ (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 12) := by
  constructor
  · -- Forward: rationality forces `n ∈ {1,2,4,12}`.
    intro hsin
    rcases lt_or_ge n 4 with hlt | hge
    · -- `n ∈ {1, 2, 3}`.
      interval_cases n
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · -- `n = 3` is impossible: `sin(2π/3)` is irrational.
        exfalso
        apply sin_two_pi_div_three_irrational
        have h3 : (2 * π / ((3 : ℕ) : ℝ)) = 2 * π / 3 := by norm_num
        rwa [h3] at hsin
    · -- `n ≥ 4`: the angle `2π/n ∈ (0, π/2]`.
      obtain ⟨r, hr⟩ := hsin
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hπ : (0 : ℝ) < π := Real.pi_pos
      have hθpos : 0 < 2 * π / (n : ℝ) := by positivity
      have hnge : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
      have hθle : 2 * π / (n : ℝ) ≤ π / 2 := by
        rw [div_le_iff₀ hnR]
        nlinarith [hπ, hnge, mul_nonneg hπ.le (by linarith : (0 : ℝ) ≤ (n : ℝ) - 4)]
      have hθltpi : 2 * π / (n : ℝ) < π := by linarith
      have hsinpos : 0 < Real.sin (2 * π / (n : ℝ)) :=
        Real.sin_pos_of_pos_of_lt_pi hθpos hθltpi
      have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hθeq : (2 * π / (n : ℝ)) = ((2 : ℤ) : ℝ) / ((n : ℤ) : ℝ) * π := by
        push_cast; ring
      have hmemI : (2 * π / (n : ℝ)) ∈ Set.Icc (-(π / 2)) (π / 2) :=
        ⟨by linarith, hθle⟩
      have hni := sin_niven (2 * π / (n : ℝ)) 2 (n : ℤ) hnz hθeq ⟨r, hr⟩
      rcases hni with h | h | h | h | h
      · exact absurd h (by linarith)
      · -- `sin = 1/2` ⟹ `2π/n = π/6` ⟹ `n = 12`.
        have h6 : Real.sin (π / 6) = 1 / 2 := Real.sin_pi_div_six
        have heq : Real.sin (2 * π / (n : ℝ)) = Real.sin (π / 6) := by rw [h, h6]
        have hmem6 : (π / 6) ∈ Set.Icc (-(π / 2)) (π / 2) :=
          ⟨by linarith, by linarith⟩
        have hxeq := Real.strictMonoOn_sin.injOn hmemI hmem6 heq
        rw [div_eq_div_iff hnR.ne' (by norm_num : (6 : ℝ) ≠ 0)] at hxeq
        -- hxeq : 2 * π * 6 = π * ↑n
        have h12 : π * 12 = π * (n : ℝ) := by linarith
        have hn12 : (12 : ℝ) = (n : ℝ) := mul_left_cancel₀ Real.pi_ne_zero h12
        have : n = 12 := by exact_mod_cast hn12.symm
        exact Or.inr (Or.inr (Or.inr this))
      · exact absurd h (by linarith)
      · -- `sin = 1` ⟹ `2π/n = π/2` ⟹ `n = 4`.
        have h2 : Real.sin (π / 2) = 1 := Real.sin_pi_div_two
        have heq : Real.sin (2 * π / (n : ℝ)) = Real.sin (π / 2) := by rw [h, h2]
        have hmem2 : (π / 2) ∈ Set.Icc (-(π / 2)) (π / 2) :=
          ⟨by linarith, le_refl _⟩
        have hxeq := Real.strictMonoOn_sin.injOn hmemI hmem2 heq
        rw [div_eq_div_iff hnR.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hxeq
        -- hxeq : 2 * π * 2 = π * ↑n
        have h4 : π * 4 = π * (n : ℝ) := by linarith
        have hn4 : (4 : ℝ) = (n : ℝ) := mul_left_cancel₀ Real.pi_ne_zero h4
        have : n = 4 := by exact_mod_cast hn4.symm
        exact Or.inr (Or.inr (Or.inl this))
      · exact absurd h (by linarith)
  · -- Reverse: explicit special-angle evaluations.
    intro hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact ⟨0, by rw [Nat.cast_one, div_one, Real.sin_two_pi]; norm_num⟩
    · refine ⟨0, ?_⟩
      have h : (2 * π / ((2 : ℕ) : ℝ)) = π := by push_cast; ring
      rw [h, Real.sin_pi]; norm_num
    · refine ⟨1, ?_⟩
      have h : (2 * π / ((4 : ℕ) : ℝ)) = π / 2 := by push_cast; ring
      rw [h, Real.sin_pi_div_two]; norm_num
    · refine ⟨1 / 2, ?_⟩
      have h : (2 * π / ((12 : ℕ) : ℝ)) = π / 6 := by push_cast; ring
      rw [h, Real.sin_pi_div_six]; norm_num

end NivenTheoremOQ01OQ03
