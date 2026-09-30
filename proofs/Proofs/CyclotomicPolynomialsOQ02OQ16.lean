/-
# OCTIC cyclotomic lemniscates: the `φ(n) = 8` layer closes (n = 15, 16, 20, 24, 30)

## What this file proves

The sextic layer (OQ14/OQ15) closed all `φ(n) = 6` cyclotomic lemniscates.
This file closes the OCTIC layer — all five `φ(n) = 8` values at once:

* `not_isPreconnected_levelSet_fifteen` … `_thirty` — `{z : ‖Φₙ(z)‖ < C}` is
  disconnected for every `0 < C < 1/1679616` and `n ∈ {15, 16, 20, 24, 30}`.
* `not_isPreconnected_levelSet_octic` — the uniform capstone (threshold
  `(1/6)⁸ = 1/1679616`), with path-connectivity corollaries throughout.

## Method: ONE radical bound replaces every minimal polynomial

The sextic sessions needed the minimal cubics of `cos (2π/9)` and `cos (2π/7)`.
The octic layer needs `cos (2π/15)` — whose minimal polynomial is an
irreducible QUARTIC — plus `cos (π/8)`, `cos (π/5)`, `cos (π/6)`.  None of
them is computed here.  The observation making that possible: with engine
radius `r = 1/6` the separation criterion `2r < dist` amounts to
`cos Δ < 17/18` for each angle gap `Δ`, and EVERY folded gap between distinct
primitive n-th roots (`n` in the octic family) is at least `π/8`:
the smallest is `2π/15 = 24° > 22.5°` (at `n = 15, 30`; coprimality disposes
of all nearer non-primitive neighbours).  Since `cos` decreases on `[0, π]`,
a single analytic input

  `cos (π/8) = √(2+√2)/2 < 17/18`   (`cos_pi_div_eight_lt`,
  half-angle formula + `√2 < 1.415` — no quartic, no heptagon trick)

drives all `5 × 7` separation branches through the shared monotonicity
criterion `cos_gap_lt : π/8 ≤ δ → δ ≤ π → cos δ < 17/18`.

Everything else is the OQ13 engine `not_isPreconnected_lemniscate` over the
abstract `primitiveRoots` factorization exactly as in OQ14/OQ15, with the
chord–cosine bridge `dist_exp_mul_I_sq` imported from OQ14.

No axioms, no sorries.
-/

import Mathlib
import Proofs.CyclotomicPolynomialsOQ02OQ13
import Proofs.CyclotomicPolynomialsOQ02OQ14

open Complex Polynomial Metric

namespace CyclotomicPolynomialsOQ02OQ16

open CyclotomicPolynomialsOQ02OQ13
open CyclotomicPolynomialsOQ02OQ14 (dist_exp_mul_I_sq)

/-! ## The one analytic input: `cos (π/8) < 17/18` -/

/-- **`cos (π/8) < 17/18`.**  Half-angle: `cos²(π/8) = 1/2 + cos(π/4)/2
= (2+√2)/4`; with `√2 < 1.415` this is `< (17/18)²`, and `cos (π/8) ≥ 0`. -/
lemma cos_pi_div_eight_lt : Real.cos (Real.pi / 8) < 17 / 18 := by
  have hsq : Real.cos (Real.pi / 8) ^ 2 = 1 / 2 + Real.cos (Real.pi / 4) / 2 := by
    have h := Real.cos_sq (Real.pi / 8)
    rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring] at h
    exact h
  rw [Real.cos_pi_div_four] at hsq
  have hs2 : Real.sqrt 2 < 1.415 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hpos : 0 ≤ Real.cos (Real.pi / 8) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  nlinarith [hsq, hs2, hpos]

/-- **The shared gap criterion**: any angle gap in `[π/8, π]` has cosine
below the `r = 1/6` separation threshold `17/18` (monotonicity of `cos`
on `[0, π]` down to `cos_pi_div_eight_lt`). -/
lemma cos_gap_lt {δ : ℝ} (h1 : Real.pi / 8 ≤ δ) (h2 : δ ≤ Real.pi) :
    Real.cos δ < 17 / 18 := by
  have hmono : Real.cos δ ≤ Real.cos (Real.pi / 8) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) h2 h1
  linarith [cos_pi_div_eight_lt]

/-- The chord criterion used with `r = 1/6`: a cosine gap below `17/18` puts
the two circle points at distance `> 1/3`. -/
lemma one_third_lt_dist_of_cos_lt {α β : ℝ} (h : Real.cos (α - β) < 17 / 18) :
    2 * (1 / 6 : ℝ) < dist (Complex.exp (↑α * Complex.I)) (Complex.exp (↑β * Complex.I)) := by
  have hd := dist_exp_mul_I_sq α β
  have h0 : (0 : ℝ) ≤ dist (Complex.exp (↑α * Complex.I)) (Complex.exp (↑β * Complex.I)) :=
    dist_nonneg
  nlinarith [hd, h, h0]

/-! ## `n = 15`: the lemniscate of `Φ₁₅` disconnects -/

/-- **The octic lemniscate `{|Φ₁₅(z)| < C}` is disconnected for
`C < 1/1679616`.**  The ball of radius `1/6` at `ζ = exp(2πi/15)` splits off:
every other primitive 15th root sits at a folded angle gap `≥ π/8`, hence at
distance `> 1/3` (`cos_gap_lt`). -/
theorem not_isPreconnected_levelSet_fifteen {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 1679616) :
    ¬ IsPreconnected {z : ℂ | ‖(cyclotomic 15 ℂ).eval z‖ < C} := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / 15)) 15 :=
    Complex.isPrimitiveRoot_exp 15 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 15) with hζdef
  have hζexp : ∀ i : ℕ, ζ ^ i = Complex.exp (↑(2 * Real.pi * i / 15) * Complex.I) := by
    intro i
    rw [hζdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hζ1 : ζ = Complex.exp (↑(2 * Real.pi / 15) * Complex.I) := by
    have h := hζexp 1
    rw [pow_one] at h
    rw [h]
    congr 2
    push_cast
    ring
  have hset : {z : ℂ | ‖(cyclotomic 15 ℂ).eval z‖ < C}
      = {z : ℂ | ‖∏ μ ∈ primitiveRoots 15 ℂ, (z - μ)‖ < C} := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hset]
  have hcard : (primitiveRoots 15 ℂ).card = 8 := by
    rw [Complex.card_primitiveRoots]
    decide
  refine not_isPreconnected_lemniscate (a := ζ) (b := ζ ^ 2) ?_ ?_ ?_ hC
    (by norm_num : (0 : ℝ) ≤ 1 / 6) ?_ ?_
  · exact (mem_primitiveRoots (by norm_num)).mpr hζ
  · exact (mem_primitiveRoots (by norm_num)).mpr
      ((hζ.pow_iff_coprime (by norm_num) 2).mpr (by decide))
  · -- `ζ^2 ≠ ζ`
    intro h
    have hne : ζ ≠ 0 := Complex.exp_ne_zero _
    have hj : ζ ^ 1 = 1 := by
      have h' : ζ * ζ ^ 1 = ζ * 1 := by
        rw [mul_one, ← pow_succ']
        exact h
      exact mul_left_cancel₀ hne h'
    have hdvd : (15 : ℕ) ∣ 1 := hζ.dvd_of_pow_eq_one 1 hj
    omega
  · rw [hcard]
    have : ((1 : ℝ) / 6) ^ 8 = 1 / 1679616 := by norm_num
    linarith
  · intro μ hμ hμζ
    haveI : NeZero (15 : ℕ) := ⟨by norm_num⟩
    have hμprim : IsPrimitiveRoot μ 15 := (mem_primitiveRoots (by norm_num)).mp hμ
    obtain ⟨i, hilt, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμprim.pow_eq_one
    have hcop : Nat.Coprime i 15 := (hζ.pow_iff_coprime (by norm_num) i).mp hμprim
    rw [dist_comm, hζexp i, hζ1]
    interval_cases i
    · exact absurd hcop (by decide)
    · exact absurd (pow_one ζ) hμζ
    · -- `i = 2`, gap `2π/15`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 2 / 15 - 2 * Real.pi / 15 = 2 * Real.pi / 15 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 4`, gap `6π/15`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 4 / 15 - 2 * Real.pi / 15 = 6 * Real.pi / 15 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 7`, gap `12π/15`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 7 / 15 - 2 * Real.pi / 15 = 12 * Real.pi / 15 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · -- `i = 8`, gap `14π/15`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 8 / 15 - 2 * Real.pi / 15 = 14 * Real.pi / 15 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 11`, reflex gap, folds to `10π/15`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 11 / 15 - 2 * Real.pi / 15 = 2 * Real.pi - 10 * Real.pi / 15 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 13`, reflex gap, folds to `6π/15`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 13 / 15 - 2 * Real.pi / 15 = 2 * Real.pi - 6 * Real.pi / 15 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · -- `i = 14`, reflex gap, folds to `4π/15`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 14 / 15 - 2 * Real.pi / 15 = 2 * Real.pi - 4 * Real.pi / 15 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- `Φ₁₅` lemniscates are not path-connected in the sub-threshold regime. -/
theorem not_isPathConnected_levelSet_fifteen {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 1679616) :
    ¬ IsPathConnected {z : ℂ | ‖(cyclotomic 15 ℂ).eval z‖ < C} :=
  fun h => not_isPreconnected_levelSet_fifteen hC hC' h.isConnected.isPreconnected

/-! ## `n = 16`: the lemniscate of `Φ₁₆` disconnects -/

/-- **The octic lemniscate `{|Φ₁₆(z)| < C}` is disconnected for
`C < 1/1679616`.**  The ball of radius `1/6` at `ζ = exp(2πi/16)` splits off:
every other primitive 16th root sits at a folded angle gap `≥ π/8`, hence at
distance `> 1/3` (`cos_gap_lt`). -/
theorem not_isPreconnected_levelSet_sixteen {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 1679616) :
    ¬ IsPreconnected {z : ℂ | ‖(cyclotomic 16 ℂ).eval z‖ < C} := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / 16)) 16 :=
    Complex.isPrimitiveRoot_exp 16 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 16) with hζdef
  have hζexp : ∀ i : ℕ, ζ ^ i = Complex.exp (↑(2 * Real.pi * i / 16) * Complex.I) := by
    intro i
    rw [hζdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hζ1 : ζ = Complex.exp (↑(2 * Real.pi / 16) * Complex.I) := by
    have h := hζexp 1
    rw [pow_one] at h
    rw [h]
    congr 2
    push_cast
    ring
  have hset : {z : ℂ | ‖(cyclotomic 16 ℂ).eval z‖ < C}
      = {z : ℂ | ‖∏ μ ∈ primitiveRoots 16 ℂ, (z - μ)‖ < C} := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hset]
  have hcard : (primitiveRoots 16 ℂ).card = 8 := by
    rw [Complex.card_primitiveRoots]
    decide
  refine not_isPreconnected_lemniscate (a := ζ) (b := ζ ^ 3) ?_ ?_ ?_ hC
    (by norm_num : (0 : ℝ) ≤ 1 / 6) ?_ ?_
  · exact (mem_primitiveRoots (by norm_num)).mpr hζ
  · exact (mem_primitiveRoots (by norm_num)).mpr
      ((hζ.pow_iff_coprime (by norm_num) 3).mpr (by decide))
  · -- `ζ^3 ≠ ζ`
    intro h
    have hne : ζ ≠ 0 := Complex.exp_ne_zero _
    have hj : ζ ^ 2 = 1 := by
      have h' : ζ * ζ ^ 2 = ζ * 1 := by
        rw [mul_one, ← pow_succ']
        exact h
      exact mul_left_cancel₀ hne h'
    have hdvd : (16 : ℕ) ∣ 2 := hζ.dvd_of_pow_eq_one 2 hj
    omega
  · rw [hcard]
    have : ((1 : ℝ) / 6) ^ 8 = 1 / 1679616 := by norm_num
    linarith
  · intro μ hμ hμζ
    haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
    have hμprim : IsPrimitiveRoot μ 16 := (mem_primitiveRoots (by norm_num)).mp hμ
    obtain ⟨i, hilt, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμprim.pow_eq_one
    have hcop : Nat.Coprime i 16 := (hζ.pow_iff_coprime (by norm_num) i).mp hμprim
    rw [dist_comm, hζexp i, hζ1]
    interval_cases i
    · exact absurd hcop (by decide)
    · exact absurd (pow_one ζ) hμζ
    · exact absurd hcop (by decide)
    · -- `i = 3`, gap `4π/16`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 3 / 16 - 2 * Real.pi / 16 = 4 * Real.pi / 16 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 5`, gap `8π/16`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 5 / 16 - 2 * Real.pi / 16 = 8 * Real.pi / 16 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 7`, gap `12π/16`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 7 / 16 - 2 * Real.pi / 16 = 12 * Real.pi / 16 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 9`, gap `16π/16`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 9 / 16 - 2 * Real.pi / 16 = 16 * Real.pi / 16 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 11`, reflex gap, folds to `12π/16`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 11 / 16 - 2 * Real.pi / 16 = 2 * Real.pi - 12 * Real.pi / 16 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 13`, reflex gap, folds to `8π/16`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 13 / 16 - 2 * Real.pi / 16 = 2 * Real.pi - 8 * Real.pi / 16 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 15`, reflex gap, folds to `4π/16`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 15 / 16 - 2 * Real.pi / 16 = 2 * Real.pi - 4 * Real.pi / 16 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- `Φ₁₆` lemniscates are not path-connected in the sub-threshold regime. -/
theorem not_isPathConnected_levelSet_sixteen {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 1679616) :
    ¬ IsPathConnected {z : ℂ | ‖(cyclotomic 16 ℂ).eval z‖ < C} :=
  fun h => not_isPreconnected_levelSet_sixteen hC hC' h.isConnected.isPreconnected

/-! ## `n = 20`: the lemniscate of `Φ₂₀` disconnects -/

/-- **The octic lemniscate `{|Φ₂₀(z)| < C}` is disconnected for
`C < 1/1679616`.**  The ball of radius `1/6` at `ζ = exp(2πi/20)` splits off:
every other primitive 20th root sits at a folded angle gap `≥ π/8`, hence at
distance `> 1/3` (`cos_gap_lt`). -/
theorem not_isPreconnected_levelSet_twenty {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 1679616) :
    ¬ IsPreconnected {z : ℂ | ‖(cyclotomic 20 ℂ).eval z‖ < C} := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / 20)) 20 :=
    Complex.isPrimitiveRoot_exp 20 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 20) with hζdef
  have hζexp : ∀ i : ℕ, ζ ^ i = Complex.exp (↑(2 * Real.pi * i / 20) * Complex.I) := by
    intro i
    rw [hζdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hζ1 : ζ = Complex.exp (↑(2 * Real.pi / 20) * Complex.I) := by
    have h := hζexp 1
    rw [pow_one] at h
    rw [h]
    congr 2
    push_cast
    ring
  have hset : {z : ℂ | ‖(cyclotomic 20 ℂ).eval z‖ < C}
      = {z : ℂ | ‖∏ μ ∈ primitiveRoots 20 ℂ, (z - μ)‖ < C} := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hset]
  have hcard : (primitiveRoots 20 ℂ).card = 8 := by
    rw [Complex.card_primitiveRoots]
    decide
  refine not_isPreconnected_lemniscate (a := ζ) (b := ζ ^ 3) ?_ ?_ ?_ hC
    (by norm_num : (0 : ℝ) ≤ 1 / 6) ?_ ?_
  · exact (mem_primitiveRoots (by norm_num)).mpr hζ
  · exact (mem_primitiveRoots (by norm_num)).mpr
      ((hζ.pow_iff_coprime (by norm_num) 3).mpr (by decide))
  · -- `ζ^3 ≠ ζ`
    intro h
    have hne : ζ ≠ 0 := Complex.exp_ne_zero _
    have hj : ζ ^ 2 = 1 := by
      have h' : ζ * ζ ^ 2 = ζ * 1 := by
        rw [mul_one, ← pow_succ']
        exact h
      exact mul_left_cancel₀ hne h'
    have hdvd : (20 : ℕ) ∣ 2 := hζ.dvd_of_pow_eq_one 2 hj
    omega
  · rw [hcard]
    have : ((1 : ℝ) / 6) ^ 8 = 1 / 1679616 := by norm_num
    linarith
  · intro μ hμ hμζ
    haveI : NeZero (20 : ℕ) := ⟨by norm_num⟩
    have hμprim : IsPrimitiveRoot μ 20 := (mem_primitiveRoots (by norm_num)).mp hμ
    obtain ⟨i, hilt, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμprim.pow_eq_one
    have hcop : Nat.Coprime i 20 := (hζ.pow_iff_coprime (by norm_num) i).mp hμprim
    rw [dist_comm, hζexp i, hζ1]
    interval_cases i
    · exact absurd hcop (by decide)
    · exact absurd (pow_one ζ) hμζ
    · exact absurd hcop (by decide)
    · -- `i = 3`, gap `4π/20`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 3 / 20 - 2 * Real.pi / 20 = 4 * Real.pi / 20 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 7`, gap `12π/20`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 7 / 20 - 2 * Real.pi / 20 = 12 * Real.pi / 20 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 9`, gap `16π/20`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 9 / 20 - 2 * Real.pi / 20 = 16 * Real.pi / 20 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 11`, gap `20π/20`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 11 / 20 - 2 * Real.pi / 20 = 20 * Real.pi / 20 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 13`, reflex gap, folds to `16π/20`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 13 / 20 - 2 * Real.pi / 20 = 2 * Real.pi - 16 * Real.pi / 20 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 17`, reflex gap, folds to `8π/20`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 17 / 20 - 2 * Real.pi / 20 = 2 * Real.pi - 8 * Real.pi / 20 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 19`, reflex gap, folds to `4π/20`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 19 / 20 - 2 * Real.pi / 20 = 2 * Real.pi - 4 * Real.pi / 20 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- `Φ₂₀` lemniscates are not path-connected in the sub-threshold regime. -/
theorem not_isPathConnected_levelSet_twenty {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 1679616) :
    ¬ IsPathConnected {z : ℂ | ‖(cyclotomic 20 ℂ).eval z‖ < C} :=
  fun h => not_isPreconnected_levelSet_twenty hC hC' h.isConnected.isPreconnected

/-! ## `n = 24`: the lemniscate of `Φ₂₄` disconnects -/

/-- **The octic lemniscate `{|Φ₂₄(z)| < C}` is disconnected for
`C < 1/1679616`.**  The ball of radius `1/6` at `ζ = exp(2πi/24)` splits off:
every other primitive 24th root sits at a folded angle gap `≥ π/8`, hence at
distance `> 1/3` (`cos_gap_lt`). -/
theorem not_isPreconnected_levelSet_twentyfour {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 1679616) :
    ¬ IsPreconnected {z : ℂ | ‖(cyclotomic 24 ℂ).eval z‖ < C} := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / 24)) 24 :=
    Complex.isPrimitiveRoot_exp 24 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 24) with hζdef
  have hζexp : ∀ i : ℕ, ζ ^ i = Complex.exp (↑(2 * Real.pi * i / 24) * Complex.I) := by
    intro i
    rw [hζdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hζ1 : ζ = Complex.exp (↑(2 * Real.pi / 24) * Complex.I) := by
    have h := hζexp 1
    rw [pow_one] at h
    rw [h]
    congr 2
    push_cast
    ring
  have hset : {z : ℂ | ‖(cyclotomic 24 ℂ).eval z‖ < C}
      = {z : ℂ | ‖∏ μ ∈ primitiveRoots 24 ℂ, (z - μ)‖ < C} := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hset]
  have hcard : (primitiveRoots 24 ℂ).card = 8 := by
    rw [Complex.card_primitiveRoots]
    decide
  refine not_isPreconnected_lemniscate (a := ζ) (b := ζ ^ 5) ?_ ?_ ?_ hC
    (by norm_num : (0 : ℝ) ≤ 1 / 6) ?_ ?_
  · exact (mem_primitiveRoots (by norm_num)).mpr hζ
  · exact (mem_primitiveRoots (by norm_num)).mpr
      ((hζ.pow_iff_coprime (by norm_num) 5).mpr (by decide))
  · -- `ζ^5 ≠ ζ`
    intro h
    have hne : ζ ≠ 0 := Complex.exp_ne_zero _
    have hj : ζ ^ 4 = 1 := by
      have h' : ζ * ζ ^ 4 = ζ * 1 := by
        rw [mul_one, ← pow_succ']
        exact h
      exact mul_left_cancel₀ hne h'
    have hdvd : (24 : ℕ) ∣ 4 := hζ.dvd_of_pow_eq_one 4 hj
    omega
  · rw [hcard]
    have : ((1 : ℝ) / 6) ^ 8 = 1 / 1679616 := by norm_num
    linarith
  · intro μ hμ hμζ
    haveI : NeZero (24 : ℕ) := ⟨by norm_num⟩
    have hμprim : IsPrimitiveRoot μ 24 := (mem_primitiveRoots (by norm_num)).mp hμ
    obtain ⟨i, hilt, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμprim.pow_eq_one
    have hcop : Nat.Coprime i 24 := (hζ.pow_iff_coprime (by norm_num) i).mp hμprim
    rw [dist_comm, hζexp i, hζ1]
    interval_cases i
    · exact absurd hcop (by decide)
    · exact absurd (pow_one ζ) hμζ
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 5`, gap `8π/24`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 5 / 24 - 2 * Real.pi / 24 = 8 * Real.pi / 24 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 7`, gap `12π/24`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 7 / 24 - 2 * Real.pi / 24 = 12 * Real.pi / 24 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 11`, gap `20π/24`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 11 / 24 - 2 * Real.pi / 24 = 20 * Real.pi / 24 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 13`, gap `24π/24`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 13 / 24 - 2 * Real.pi / 24 = 24 * Real.pi / 24 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 17`, reflex gap, folds to `16π/24`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 17 / 24 - 2 * Real.pi / 24 = 2 * Real.pi - 16 * Real.pi / 24 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 19`, reflex gap, folds to `12π/24`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 19 / 24 - 2 * Real.pi / 24 = 2 * Real.pi - 12 * Real.pi / 24 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 23`, reflex gap, folds to `4π/24`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 23 / 24 - 2 * Real.pi / 24 = 2 * Real.pi - 4 * Real.pi / 24 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- `Φ₂₄` lemniscates are not path-connected in the sub-threshold regime. -/
theorem not_isPathConnected_levelSet_twentyfour {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 1679616) :
    ¬ IsPathConnected {z : ℂ | ‖(cyclotomic 24 ℂ).eval z‖ < C} :=
  fun h => not_isPreconnected_levelSet_twentyfour hC hC' h.isConnected.isPreconnected

/-! ## `n = 30`: the lemniscate of `Φ₃₀` disconnects -/

/-- **The octic lemniscate `{|Φ₃₀(z)| < C}` is disconnected for
`C < 1/1679616`.**  The ball of radius `1/6` at `ζ = exp(2πi/30)` splits off:
every other primitive 30th root sits at a folded angle gap `≥ π/8`, hence at
distance `> 1/3` (`cos_gap_lt`). -/
theorem not_isPreconnected_levelSet_thirty {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 1679616) :
    ¬ IsPreconnected {z : ℂ | ‖(cyclotomic 30 ℂ).eval z‖ < C} := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / 30)) 30 :=
    Complex.isPrimitiveRoot_exp 30 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 30) with hζdef
  have hζexp : ∀ i : ℕ, ζ ^ i = Complex.exp (↑(2 * Real.pi * i / 30) * Complex.I) := by
    intro i
    rw [hζdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hζ1 : ζ = Complex.exp (↑(2 * Real.pi / 30) * Complex.I) := by
    have h := hζexp 1
    rw [pow_one] at h
    rw [h]
    congr 2
    push_cast
    ring
  have hset : {z : ℂ | ‖(cyclotomic 30 ℂ).eval z‖ < C}
      = {z : ℂ | ‖∏ μ ∈ primitiveRoots 30 ℂ, (z - μ)‖ < C} := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hset]
  have hcard : (primitiveRoots 30 ℂ).card = 8 := by
    rw [Complex.card_primitiveRoots]
    decide
  refine not_isPreconnected_lemniscate (a := ζ) (b := ζ ^ 7) ?_ ?_ ?_ hC
    (by norm_num : (0 : ℝ) ≤ 1 / 6) ?_ ?_
  · exact (mem_primitiveRoots (by norm_num)).mpr hζ
  · exact (mem_primitiveRoots (by norm_num)).mpr
      ((hζ.pow_iff_coprime (by norm_num) 7).mpr (by decide))
  · -- `ζ^7 ≠ ζ`
    intro h
    have hne : ζ ≠ 0 := Complex.exp_ne_zero _
    have hj : ζ ^ 6 = 1 := by
      have h' : ζ * ζ ^ 6 = ζ * 1 := by
        rw [mul_one, ← pow_succ']
        exact h
      exact mul_left_cancel₀ hne h'
    have hdvd : (30 : ℕ) ∣ 6 := hζ.dvd_of_pow_eq_one 6 hj
    omega
  · rw [hcard]
    have : ((1 : ℝ) / 6) ^ 8 = 1 / 1679616 := by norm_num
    linarith
  · intro μ hμ hμζ
    haveI : NeZero (30 : ℕ) := ⟨by norm_num⟩
    have hμprim : IsPrimitiveRoot μ 30 := (mem_primitiveRoots (by norm_num)).mp hμ
    obtain ⟨i, hilt, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμprim.pow_eq_one
    have hcop : Nat.Coprime i 30 := (hζ.pow_iff_coprime (by norm_num) i).mp hμprim
    rw [dist_comm, hζexp i, hζ1]
    interval_cases i
    · exact absurd hcop (by decide)
    · exact absurd (pow_one ζ) hμζ
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 7`, gap `12π/30`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 7 / 30 - 2 * Real.pi / 30 = 12 * Real.pi / 30 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 11`, gap `20π/30`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 11 / 30 - 2 * Real.pi / 30 = 20 * Real.pi / 30 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 13`, gap `24π/30`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 13 / 30 - 2 * Real.pi / 30 = 24 * Real.pi / 30 by ring]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 17`, reflex gap, folds to `28π/30`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 17 / 30 - 2 * Real.pi / 30 = 2 * Real.pi - 28 * Real.pi / 30 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · -- `i = 19`, reflex gap, folds to `24π/30`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 19 / 30 - 2 * Real.pi / 30 = 2 * Real.pi - 24 * Real.pi / 30 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 23`, reflex gap, folds to `16π/30`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 23 / 30 - 2 * Real.pi / 30 = 2 * Real.pi - 16 * Real.pi / 30 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 29`, reflex gap, folds to `4π/30`
      apply one_third_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 29 / 30 - 2 * Real.pi / 30 = 2 * Real.pi - 4 * Real.pi / 30 by ring, Real.cos_two_pi_sub]
      exact cos_gap_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- `Φ₃₀` lemniscates are not path-connected in the sub-threshold regime. -/
theorem not_isPathConnected_levelSet_thirty {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 1679616) :
    ¬ IsPathConnected {z : ℂ | ‖(cyclotomic 30 ℂ).eval z‖ < C} :=
  fun h => not_isPreconnected_levelSet_thirty hC hC' h.isConnected.isPreconnected

/-! ## The octic capstone -/

/-- **The `φ(n) = 8` layer is CLOSED**: for every `n` with `φ(n) = 8` — i.e.
`n ∈ {15, 16, 20, 24, 30}` — the cyclotomic lemniscate `{z : ‖Φₙ(z)‖ < C}` is
disconnected for every `0 < C < 1/1679616` (uniform threshold `(1/6)⁸`). -/
theorem not_isPreconnected_levelSet_octic {n : ℕ}
    (hn : n ∈ ({15, 16, 20, 24, 30} : Finset ℕ)) {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 1679616) :
    ¬ IsPreconnected {z : ℂ | ‖(cyclotomic n ℂ).eval z‖ < C} := by
  fin_cases hn
  · exact not_isPreconnected_levelSet_fifteen hC hC'
  · exact not_isPreconnected_levelSet_sixteen hC hC'
  · exact not_isPreconnected_levelSet_twenty hC hC'
  · exact not_isPreconnected_levelSet_twentyfour hC hC'
  · exact not_isPreconnected_levelSet_thirty hC hC'

/-- Path-connectivity form of the octic capstone. -/
theorem not_isPathConnected_levelSet_octic {n : ℕ}
    (hn : n ∈ ({15, 16, 20, 24, 30} : Finset ℕ)) {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 1679616) :
    ¬ IsPathConnected {z : ℂ | ‖(cyclotomic n ℂ).eval z‖ < C} :=
  fun h => not_isPreconnected_levelSet_octic hn hC hC' h.isConnected.isPreconnected

#check @cos_pi_div_eight_lt
#check @cos_gap_lt
#check @not_isPreconnected_levelSet_fifteen
#check @not_isPreconnected_levelSet_sixteen
#check @not_isPreconnected_levelSet_twenty
#check @not_isPreconnected_levelSet_twentyfour
#check @not_isPreconnected_levelSet_thirty
#check @not_isPreconnected_levelSet_octic
#check @not_isPathConnected_levelSet_octic

end CyclotomicPolynomialsOQ02OQ16
