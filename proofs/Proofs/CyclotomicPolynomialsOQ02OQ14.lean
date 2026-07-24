/-
# SEXTIC cyclotomic lemniscates: the `φ(n) = 6` layer opens (n = 9, 18)

## What this file proves

The quartic layer (OQ13) closed all `φ(n) = 4` cyclotomic lemniscates with the
degree-generic disconnection engine `not_isPreconnected_lemniscate`.  This file
opens the SEXTIC layer at the two `φ(n) = 6` values whose cosines are reachable
by the triple-angle formula — `n = 9` and `n = 18`:

* `not_isPreconnected_levelSet_nine`   — `{z : ‖Φ₉(z)‖ < C}` is disconnected
  for every `0 < C < 1/15625`.
* `not_isPreconnected_levelSet_eighteen` — likewise for `Φ₁₈`.
* Path-connectivity corollaries for both.

## Method: no radicals, no explicit root list

Unlike `n = 8, 12` (whose roots are radical expressions), the primitive 9th and
18th roots of unity involve `cos (2π/9)`, whose minimal polynomial is an
irreducible cubic — no explicit surd form exists.  The engine never needs one:

1. `cyclotomic_eq_prod_X_sub_primitiveRoots` factors `Φ_n` over
   `S = primitiveRoots n ℂ` abstractly; `|S| = φ(n) = 6`.
2. Every member of `S` is `ζⁱ` for `ζ = exp(2πi/n)` and `i` COPRIME to `n`
   (`eq_pow_of_pow_eq_one` + `pow_iff_coprime`) — coprimality kills the
   dangerously close non-primitive neighbours (for `n = 18` the nearest
   primitive root sits `80°` away, not `20°`).
3. Distances on the unit circle reduce to cosines:
   `dist(exp(αi), exp(βi))² = 2 − 2cos(α−β)` (`dist_exp_mul_I_sq`), so the
   separation hypothesis `2r < dist` with `r = 1/5` becomes
   `cos Δ < 23/25` for each angle gap `Δ`.
4. Every needed gap bound follows from ONE analytic fact,
   `cos (2π/9) < 5/6` (`cos_two_pi_div_nine_lt`), proved from the
   triple-angle identity `4c³ − 3c = cos(2π/3) = −1/2` by isolating the root
   with an exact factorization at `c = 5/6` — plus sign/monotonicity
   trivialities (`cos(2π/3) = cos(4π/3) = −1/2`, `cos(8π/9) < 0`,
   `cos(4π/9) < cos(2π/9)`).

The remaining sextic values `n = 7, 14` need `cos(2π/7)` (minimal cubic
`8x³ + 4x² − 4x − 1`, NOT a triple-angle instance) — left to a future session.

No axioms, no sorries; everything is elementary complex analysis over the
OQ13 engine.
-/

import Mathlib
import Proofs.CyclotomicPolynomialsOQ02OQ13

open Complex Polynomial Metric

namespace CyclotomicPolynomialsOQ02OQ14

open CyclotomicPolynomialsOQ02OQ13

/-! ## Circle distances via cosine gaps -/

/-- Squared chord length on the unit circle: `|exp(αi) − exp(βi)|² = 2 − 2cos(α−β)`. -/
lemma dist_exp_mul_I_sq (α β : ℝ) :
    dist (Complex.exp (↑α * Complex.I)) (Complex.exp (↑β * Complex.I)) ^ 2
      = 2 - 2 * Real.cos (α - β) := by
  rw [dist_eq_norm, Complex.sq_norm]
  have ha : Complex.exp (↑α * Complex.I)
      = ↑(Real.cos α) + ↑(Real.sin α) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hb : Complex.exp (↑β * Complex.I)
      = ↑(Real.cos β) + ↑(Real.sin β) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hsub : (↑(Real.cos α) + ↑(Real.sin α) * Complex.I)
        - (↑(Real.cos β) + ↑(Real.sin β) * Complex.I)
      = ↑(Real.cos α - Real.cos β) + ↑(Real.sin α - Real.sin β) * Complex.I := by
    push_cast
    ring
  rw [ha, hb, hsub, Complex.normSq_add_mul_I, Real.cos_sub]
  have h1 := Real.sin_sq_add_cos_sq α
  have h2 := Real.sin_sq_add_cos_sq β
  ring_nf
  nlinarith [h1, h2]

/-- The chord criterion used with `r = 1/5`: a cosine gap below `23/25` puts the
two circle points at distance `> 2/5`. -/
lemma two_fifths_lt_dist_of_cos_lt {α β : ℝ} (h : Real.cos (α - β) < 23 / 25) :
    2 * (1 / 5 : ℝ) < dist (Complex.exp (↑α * Complex.I)) (Complex.exp (↑β * Complex.I)) := by
  have hd := dist_exp_mul_I_sq α β
  have h0 : (0 : ℝ) ≤ dist (Complex.exp (↑α * Complex.I)) (Complex.exp (↑β * Complex.I)) :=
    dist_nonneg
  nlinarith [hd, h, h0]

/-! ## The one analytic input: `cos (2π/9) < 5/6` -/

/-- **`cos (2π/9) < 5/6`.**  From the triple-angle identity
`4c³ − 3c = cos(2π/3) = −1/2` and the exact factorization
`4c³ − 3c + 5/27 = (c − 5/6)(4c² + (10/3)c − 2/9)`, whose second factor is
positive for `c ≥ 5/6`: a root `≥ 5/6` would make `4c³ − 3c ≥ −5/27 > −1/2`. -/
lemma cos_two_pi_div_nine_lt : Real.cos (2 * Real.pi / 9) < 5 / 6 := by
  have h3 : Real.cos (3 * (2 * Real.pi / 9)) = -(1 / 2) := by
    rw [show 3 * (2 * Real.pi / 9) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
  have hcube := Real.cos_three_mul (2 * Real.pi / 9)
  rw [h3] at hcube
  set c := Real.cos (2 * Real.pi / 9) with hc
  by_contra hcon
  push Not at hcon
  have hfac : 4 * c ^ 3 - 3 * c + 5 / 27
      = (c - 5 / 6) * (4 * c ^ 2 + (10 / 3) * c - 2 / 9) := by ring
  have hpos : (0 : ℝ) ≤ 4 * c ^ 2 + (10 / 3) * c - 2 / 9 := by nlinarith [hcon]
  have hnonneg : (0 : ℝ) ≤ (c - 5 / 6) * (4 * c ^ 2 + (10 / 3) * c - 2 / 9) :=
    mul_nonneg (by linarith) hpos
  nlinarith [hcube, hnonneg, hfac]

/-- `cos (4π/9) < 5/6`, by monotonicity from `cos (2π/9)`. -/
lemma cos_four_pi_div_nine_lt : Real.cos (4 * Real.pi / 9) < 5 / 6 := by
  have hmono : Real.cos (4 * Real.pi / 9) < Real.cos (2 * Real.pi / 9) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · positivity
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  linarith [cos_two_pi_div_nine_lt]

/-- `cos (2π/3) = −1/2`. -/
lemma cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]

/-- `cos (4π/3) = −1/2`. -/
lemma cos_four_pi_div_three : Real.cos (4 * Real.pi / 3) = -(1 / 2) := by
  rw [show 4 * Real.pi / 3 = 2 * Real.pi - 2 * Real.pi / 3 by ring, Real.cos_two_pi_sub,
    cos_two_pi_div_three]

/-- `cos (8π/9) < 0`. -/
lemma cos_eight_pi_div_nine_neg : Real.cos (8 * Real.pi / 9) < 0 := by
  rw [show 8 * Real.pi / 9 = Real.pi - Real.pi / 9 by ring, Real.cos_pi_sub]
  have : 0 < Real.cos (Real.pi / 9) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  linarith

/-! ## `n = 9`: the lemniscate of `Φ₉` disconnects -/

/-- **The sextic lemniscate `{|Φ₉(z)| < C}` is disconnected for `C < 1/15625`.**
The ball of radius `1/5` at `ζ₉ = exp(2πi/9)` splits off: every other primitive
9th root `ζ₉ⁱ` (`i ∈ {2,4,5,7,8}`) has angle gap `≥ 2π/9` with cosine `< 23/25`,
hence distance `> 2/5`. -/
theorem not_isPreconnected_levelSet_nine {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 15625) :
    ¬ IsPreconnected {z : ℂ | ‖(cyclotomic 9 ℂ).eval z‖ < C} := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / 9)) 9 :=
    Complex.isPrimitiveRoot_exp 9 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 9) with hζdef
  have hζexp : ∀ i : ℕ, ζ ^ i = Complex.exp (↑(2 * Real.pi * i / 9) * Complex.I) := by
    intro i
    rw [hζdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hζ1 : ζ = Complex.exp (↑(2 * Real.pi / 9) * Complex.I) := by
    have h := hζexp 1
    rw [pow_one] at h
    rw [h]
    congr 2
    push_cast
    ring
  -- Rewrite the level set through the primitive-root factorization.
  have hset : {z : ℂ | ‖(cyclotomic 9 ℂ).eval z‖ < C}
      = {z : ℂ | ‖∏ μ ∈ primitiveRoots 9 ℂ, (z - μ)‖ < C} := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hset]
  have hcard : (primitiveRoots 9 ℂ).card = 6 := by
    rw [Complex.card_primitiveRoots]
    decide
  refine not_isPreconnected_lemniscate (a := ζ) (b := ζ ^ 2) ?_ ?_ ?_ hC
    (by norm_num : (0 : ℝ) ≤ 1 / 5) ?_ ?_
  · exact (mem_primitiveRoots (by norm_num)).mpr hζ
  · exact (mem_primitiveRoots (by norm_num)).mpr
      ((hζ.pow_iff_coprime (by norm_num) 2).mpr (by decide))
  · -- `ζ² ≠ ζ`
    intro h
    have hne : ζ ≠ 0 := Complex.exp_ne_zero _
    have hone : ζ = 1 := by
      have h2 : ζ * ζ = ζ * 1 := by rw [mul_one, ← sq]; exact h
      exact mul_left_cancel₀ hne h2
    exact hζ.ne_one (by norm_num) hone
  · rw [hcard]
    have : ((1 : ℝ) / 5) ^ 6 = 1 / 15625 := by norm_num
    linarith
  · -- Separation: every other primitive root is at distance `> 2/5` from `ζ`.
    intro μ hμ hμζ
    haveI : NeZero (9 : ℕ) := ⟨by norm_num⟩
    have hμprim : IsPrimitiveRoot μ 9 := (mem_primitiveRoots (by norm_num)).mp hμ
    obtain ⟨i, hi9, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμprim.pow_eq_one
    have hcop : Nat.Coprime i 9 := (hζ.pow_iff_coprime (by norm_num) i).mp hμprim
    rw [dist_comm, hζexp i, hζ1]
    interval_cases i
    · exact absurd hcop (by decide)
    · exact absurd (pow_one ζ) hμζ
    · -- `i = 2`, gap `2π/9`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 2 / 9 - 2 * Real.pi / 9 = 2 * Real.pi / 9 by ring]
      linarith [cos_two_pi_div_nine_lt]
    · exact absurd hcop (by decide)
    · -- `i = 4`, gap `2π/3`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 4 / 9 - 2 * Real.pi / 9 = 2 * Real.pi / 3 by ring,
        cos_two_pi_div_three]
      norm_num
    · -- `i = 5`, gap `8π/9`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 5 / 9 - 2 * Real.pi / 9 = 8 * Real.pi / 9 by ring]
      linarith [cos_eight_pi_div_nine_neg]
    · exact absurd hcop (by decide)
    · -- `i = 7`, gap `4π/3`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 7 / 9 - 2 * Real.pi / 9 = 4 * Real.pi / 3 by ring,
        cos_four_pi_div_three]
      norm_num
    · -- `i = 8`, gap `14π/9`, cosine equals `cos (4π/9)`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 8 / 9 - 2 * Real.pi / 9 = 2 * Real.pi - 4 * Real.pi / 9 by ring,
        Real.cos_two_pi_sub]
      linarith [cos_four_pi_div_nine_lt]

/-- `Φ₉` lemniscates are not path-connected in the sub-threshold regime. -/
theorem not_isPathConnected_levelSet_nine {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 15625) :
    ¬ IsPathConnected {z : ℂ | ‖(cyclotomic 9 ℂ).eval z‖ < C} :=
  fun h => not_isPreconnected_levelSet_nine hC hC' h.isConnected.isPreconnected

/-! ## `n = 18`: the lemniscate of `Φ₁₈` disconnects -/

/-- **The sextic lemniscate `{|Φ₁₈(z)| < C}` is disconnected for `C < 1/15625`.**
Same engine at `ζ₁₈ = exp(πi/9)`.  Coprimality is what makes the radius work:
the nearest 18th roots of unity (`20°` away) are NOT primitive; the nearest
primitive ones (`i = 5, 17`) sit at angle gap `4π/9` resp. `2π/9`. -/
theorem not_isPreconnected_levelSet_eighteen {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 15625) :
    ¬ IsPreconnected {z : ℂ | ‖(cyclotomic 18 ℂ).eval z‖ < C} := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / 18)) 18 :=
    Complex.isPrimitiveRoot_exp 18 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 18) with hζdef
  have hζexp : ∀ i : ℕ, ζ ^ i = Complex.exp (↑(2 * Real.pi * i / 18) * Complex.I) := by
    intro i
    rw [hζdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hζ1 : ζ = Complex.exp (↑(2 * Real.pi / 18) * Complex.I) := by
    have h := hζexp 1
    rw [pow_one] at h
    rw [h]
    congr 2
    push_cast
    ring
  have hset : {z : ℂ | ‖(cyclotomic 18 ℂ).eval z‖ < C}
      = {z : ℂ | ‖∏ μ ∈ primitiveRoots 18 ℂ, (z - μ)‖ < C} := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hset]
  have hcard : (primitiveRoots 18 ℂ).card = 6 := by
    rw [Complex.card_primitiveRoots]
    decide
  refine not_isPreconnected_lemniscate (a := ζ) (b := ζ ^ 5) ?_ ?_ ?_ hC
    (by norm_num : (0 : ℝ) ≤ 1 / 5) ?_ ?_
  · exact (mem_primitiveRoots (by norm_num)).mpr hζ
  · exact (mem_primitiveRoots (by norm_num)).mpr
      ((hζ.pow_iff_coprime (by norm_num) 5).mpr (by decide))
  · -- `ζ⁵ ≠ ζ`
    intro h
    have hne : ζ ≠ 0 := Complex.exp_ne_zero _
    have h4 : ζ ^ 4 = 1 := by
      have h5 : ζ * ζ ^ 4 = ζ * 1 := by
        rw [mul_one, ← pow_succ']
        exact h
      exact mul_left_cancel₀ hne h5
    have : (18 : ℕ) ∣ 4 := hζ.dvd_of_pow_eq_one 4 h4
    omega
  · rw [hcard]
    have : ((1 : ℝ) / 5) ^ 6 = 1 / 15625 := by norm_num
    linarith
  · intro μ hμ hμζ
    haveI : NeZero (18 : ℕ) := ⟨by norm_num⟩
    have hμprim : IsPrimitiveRoot μ 18 := (mem_primitiveRoots (by norm_num)).mp hμ
    obtain ⟨i, hi18, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμprim.pow_eq_one
    have hcop : Nat.Coprime i 18 := (hζ.pow_iff_coprime (by norm_num) i).mp hμprim
    rw [dist_comm, hζexp i, hζ1]
    interval_cases i
    · exact absurd hcop (by decide)
    · exact absurd (pow_one ζ) hμζ
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 5`, gap `4π/9`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 5 / 18 - 2 * Real.pi / 18 = 4 * Real.pi / 9 by ring]
      linarith [cos_four_pi_div_nine_lt]
    · exact absurd hcop (by decide)
    · -- `i = 7`, gap `2π/3`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 7 / 18 - 2 * Real.pi / 18 = 2 * Real.pi / 3 by ring,
        cos_two_pi_div_three]
      norm_num
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 11`, gap `10π/9`, cosine equals `cos (8π/9)`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 11 / 18 - 2 * Real.pi / 18 = 2 * Real.pi - 8 * Real.pi / 9 by ring,
        Real.cos_two_pi_sub]
      linarith [cos_eight_pi_div_nine_neg]
    · exact absurd hcop (by decide)
    · -- `i = 13`, gap `4π/3`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 13 / 18 - 2 * Real.pi / 18 = 4 * Real.pi / 3 by ring,
        cos_four_pi_div_three]
      norm_num
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 17`, gap `16π/9`, cosine equals `cos (2π/9)`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 17 / 18 - 2 * Real.pi / 18 = 2 * Real.pi - 2 * Real.pi / 9 by ring,
        Real.cos_two_pi_sub]
      linarith [cos_two_pi_div_nine_lt]

/-- `Φ₁₈` lemniscates are not path-connected in the sub-threshold regime. -/
theorem not_isPathConnected_levelSet_eighteen {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 15625) :
    ¬ IsPathConnected {z : ℂ | ‖(cyclotomic 18 ℂ).eval z‖ < C} :=
  fun h => not_isPreconnected_levelSet_eighteen hC hC' h.isConnected.isPreconnected

#check @dist_exp_mul_I_sq
#check @cos_two_pi_div_nine_lt
#check @not_isPreconnected_levelSet_nine
#check @not_isPreconnected_levelSet_eighteen
#check @not_isPathConnected_levelSet_nine
#check @not_isPathConnected_levelSet_eighteen

end CyclotomicPolynomialsOQ02OQ14
