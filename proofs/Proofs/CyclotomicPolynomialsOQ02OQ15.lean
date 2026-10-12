/-
# SEXTIC cyclotomic lemniscates COMPLETE: `n = 7, 14` close the `φ(n) = 6` layer

## What this file proves

OQ14 opened the sextic layer at `n = 9, 18` (the two `φ(n) = 6` values whose
cosines are triple-angle reachable).  This file closes the layer at the
remaining two values `n = 7, 14`:

* `not_isPreconnected_levelSet_seven`    — `{z : ‖Φ₇(z)‖ < C}` is disconnected
  for every `0 < C < 1/15625`.
* `not_isPreconnected_levelSet_fourteen` — likewise for `Φ₁₄`.
* Path-connectivity corollaries for both.
* `not_isPreconnected_levelSet_sextic`   — the uniform capstone: ALL four
  `φ(n) = 6` values `n ∈ {7, 9, 14, 18}` disconnect below the common
  threshold `C = 1/15625`.  The sextic layer is now closed in the same sense
  the quartic layer was closed by OQ13's `not_isPreconnected_levelSet_quartic`.

## Method: the minimal cubic of `cos (2π/7)`

`cos (2π/7)` is NOT a triple-angle instance (its minimal polynomial is the
irreducible cubic `8x³ + 4x² − 4x − 1`), so OQ14's route via
`cos 3θ = −1/2` does not apply.  Instead we derive the cubic from scratch:

1. For `θ = 2π/7` we have `4θ + 3θ = 2π`, hence `cos 4θ = cos 3θ`
   (`Real.cos_two_pi_sub`) — the classical heptagon trick.
2. `cos 4θ = 2(2c² − 1)² − 1` (double angle twice) and `cos 3θ = 4c³ − 3c`
   (`Real.cos_three_mul`) turn this into the quartic
   `8c⁴ − 4c³ − 8c² + 3c + 1 = 0`, which factors EXACTLY as
   `(c − 1)(8c³ + 4c² − 4c − 1) = 0`; since `c = cos (2π/7) < 1` the cubic
   factor vanishes (`cos_two_pi_div_seven_cubic`) — a byproduct absent from
   Mathlib.
3. The engine bound `cos (2π/7) < 23/25` follows by isolating the root with
   an exact polynomial division at `23/25`:
   `p(c) − 77111/15625 = (c − 23/25)(8c² + (284/25)c + 4032/625)`, whose
   second factor is positive — a root `≥ 23/25` would make `p(c) > 0`.
4. All remaining angle gaps have NEGATIVE cosines (`cos (4π/7)`,
   `cos (6π/7) < 0` via `cos (π − x)`), so the single cubic bound powers both
   `n = 7` (gaps `2πj/7`) and `n = 14` (primitive gaps `2πj/7` again —
   coprimality to `14` kills the `20°`-class non-primitive neighbours exactly
   as at `n = 18`).

Everything runs through the OQ13 degree-generic engine
`not_isPreconnected_lemniscate` with `r = 1/5`, `C ≤ (1/5)⁶ = 1/15625`, and
OQ14's chord-cosine reduction `dist² = 2 − 2cos Δ`.

No axioms, no sorries.
-/

import Mathlib
import Proofs.CyclotomicPolynomialsOQ02OQ14

open Complex Polynomial Metric

namespace CyclotomicPolynomialsOQ02OQ15

open CyclotomicPolynomialsOQ02OQ13 CyclotomicPolynomialsOQ02OQ14

/-! ## The minimal cubic of `cos (2π/7)` -/

/-- **`cos (2π/7)` is a root of `8x³ + 4x² − 4x − 1`** (its minimal cubic —
not in Mathlib).  From `4θ = 2π − 3θ` at `θ = 2π/7`: `cos 4θ = cos 3θ`
becomes the quartic `8c⁴ − 4c³ − 8c² + 3c + 1 = 0`, which factors as
`(c − 1)(8c³ + 4c² − 4c − 1)`; the first factor is nonzero since `c < 1`. -/
lemma cos_two_pi_div_seven_cubic :
    8 * Real.cos (2 * Real.pi / 7) ^ 3 + 4 * Real.cos (2 * Real.pi / 7) ^ 2
      - 4 * Real.cos (2 * Real.pi / 7) - 1 = 0 := by
  have h43 : Real.cos (4 * (2 * Real.pi / 7)) = Real.cos (3 * (2 * Real.pi / 7)) := by
    rw [show 4 * (2 * Real.pi / 7) = 2 * Real.pi - 3 * (2 * Real.pi / 7) by ring,
      Real.cos_two_pi_sub]
  have h4 : Real.cos (4 * (2 * Real.pi / 7))
      = 2 * Real.cos (2 * (2 * Real.pi / 7)) ^ 2 - 1 := by
    rw [show (4 : ℝ) * (2 * Real.pi / 7) = 2 * (2 * (2 * Real.pi / 7)) by ring,
      Real.cos_two_mul]
  have h2 := Real.cos_two_mul (2 * Real.pi / 7)
  have h3 := Real.cos_three_mul (2 * Real.pi / 7)
  rw [h4, h2, h3] at h43
  set c := Real.cos (2 * Real.pi / 7) with hc
  -- h43 : 2 * (2 * c ^ 2 - 1) ^ 2 - 1 = 4 * c ^ 3 - 3 * c
  have hlt : c < 1 := by
    have hmono : Real.cos (2 * Real.pi / 7) < Real.cos 0 := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      · exact le_refl 0
      · nlinarith [Real.pi_pos]
      · positivity
    rw [Real.cos_zero] at hmono
    rw [hc]
    exact hmono
  have hquart : (c - 1) * (8 * c ^ 3 + 4 * c ^ 2 - 4 * c - 1) = 0 := by
    linear_combination h43
  have hne : c - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hlt)
  rcases mul_eq_zero.mp hquart with h | h
  · exact absurd h hne
  · exact h

/-- **`cos (2π/7) < 23/25`** — the one analytic input the engine needs.
Root isolation by exact polynomial division of the minimal cubic at `23/25`:
`p(c) − 77111/15625 = (c − 23/25)(8c² + (284/25)c + 4032/625)`, second factor
positive, so a root `≥ 23/25` would force `p(c) ≥ 77111/15625 > 0`. -/
lemma cos_two_pi_div_seven_lt : Real.cos (2 * Real.pi / 7) < 23 / 25 := by
  have hcubic := cos_two_pi_div_seven_cubic
  set c := Real.cos (2 * Real.pi / 7) with hc
  by_contra hcon
  push Not at hcon
  have hfac : 8 * c ^ 3 + 4 * c ^ 2 - 4 * c - 1 - 77111 / 15625
      = (c - 23 / 25) * (8 * c ^ 2 + (284 / 25) * c + 4032 / 625) := by ring
  have hpos : (0 : ℝ) ≤ 8 * c ^ 2 + (284 / 25) * c + 4032 / 625 := by nlinarith [hcon]
  have hnonneg : (0 : ℝ) ≤ (c - 23 / 25) * (8 * c ^ 2 + (284 / 25) * c + 4032 / 625) :=
    mul_nonneg (by linarith) hpos
  nlinarith [hcubic, hnonneg, hfac]

/-- `cos (4π/7) < 0`: reflection `4π/7 = π − 3π/7` and `cos (3π/7) > 0`. -/
lemma cos_four_pi_div_seven_neg : Real.cos (4 * Real.pi / 7) < 0 := by
  rw [show 4 * Real.pi / 7 = Real.pi - 3 * Real.pi / 7 by ring, Real.cos_pi_sub]
  have : 0 < Real.cos (3 * Real.pi / 7) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  linarith

/-- `cos (6π/7) < 0`: reflection `6π/7 = π − π/7` and `cos (π/7) > 0`. -/
lemma cos_six_pi_div_seven_neg : Real.cos (6 * Real.pi / 7) < 0 := by
  rw [show 6 * Real.pi / 7 = Real.pi - Real.pi / 7 by ring, Real.cos_pi_sub]
  have : 0 < Real.cos (Real.pi / 7) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  linarith

/-! ## `n = 7`: the lemniscate of `Φ₇` disconnects -/

/-- **The sextic lemniscate `{|Φ₇(z)| < C}` is disconnected for `C < 1/15625`.**
The ball of radius `1/5` at `ζ₇ = exp(2πi/7)` splits off: every other primitive
7th root `ζ₇ⁱ` (`i ∈ {2,…,6}`) has angle gap in `{2π/7, 4π/7, 6π/7}` (up to
reflection), each with cosine `< 23/25`, hence distance `> 2/5`. -/
theorem not_isPreconnected_levelSet_seven {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 15625) :
    ¬ IsPreconnected {z : ℂ | ‖(cyclotomic 7 ℂ).eval z‖ < C} := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / 7)) 7 :=
    Complex.isPrimitiveRoot_exp 7 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 7) with hζdef
  have hζexp : ∀ i : ℕ, ζ ^ i = Complex.exp (↑(2 * Real.pi * i / 7) * Complex.I) := by
    intro i
    rw [hζdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hζ1 : ζ = Complex.exp (↑(2 * Real.pi / 7) * Complex.I) := by
    have h := hζexp 1
    rw [pow_one] at h
    rw [h]
    congr 2
    push_cast
    ring
  have hset : {z : ℂ | ‖(cyclotomic 7 ℂ).eval z‖ < C}
      = {z : ℂ | ‖∏ μ ∈ primitiveRoots 7 ℂ, (z - μ)‖ < C} := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hset]
  have hcard : (primitiveRoots 7 ℂ).card = 6 := by
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
    haveI : NeZero (7 : ℕ) := ⟨by norm_num⟩
    have hμprim : IsPrimitiveRoot μ 7 := (mem_primitiveRoots (by norm_num)).mp hμ
    obtain ⟨i, hi7, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμprim.pow_eq_one
    have hcop : Nat.Coprime i 7 := (hζ.pow_iff_coprime (by norm_num) i).mp hμprim
    rw [dist_comm, hζexp i, hζ1]
    interval_cases i
    · exact absurd hcop (by decide)
    · exact absurd (pow_one ζ) hμζ
    · -- `i = 2`, gap `2π/7`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 2 / 7 - 2 * Real.pi / 7 = 2 * Real.pi / 7 by ring]
      linarith [cos_two_pi_div_seven_lt]
    · -- `i = 3`, gap `4π/7`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 3 / 7 - 2 * Real.pi / 7 = 4 * Real.pi / 7 by ring]
      linarith [cos_four_pi_div_seven_neg]
    · -- `i = 4`, gap `6π/7`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 4 / 7 - 2 * Real.pi / 7 = 6 * Real.pi / 7 by ring]
      linarith [cos_six_pi_div_seven_neg]
    · -- `i = 5`, gap `8π/7`, cosine equals `cos (6π/7)`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 5 / 7 - 2 * Real.pi / 7 = 2 * Real.pi - 6 * Real.pi / 7 by ring,
        Real.cos_two_pi_sub]
      linarith [cos_six_pi_div_seven_neg]
    · -- `i = 6`, gap `10π/7`, cosine equals `cos (4π/7)`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 6 / 7 - 2 * Real.pi / 7 = 2 * Real.pi - 4 * Real.pi / 7 by ring,
        Real.cos_two_pi_sub]
      linarith [cos_four_pi_div_seven_neg]

/-- `Φ₇` lemniscates are not path-connected in the sub-threshold regime. -/
theorem not_isPathConnected_levelSet_seven {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 15625) :
    ¬ IsPathConnected {z : ℂ | ‖(cyclotomic 7 ℂ).eval z‖ < C} :=
  fun h => not_isPreconnected_levelSet_seven hC hC' h.isConnected.isPreconnected

/-! ## `n = 14`: the lemniscate of `Φ₁₄` disconnects -/

/-- **The sextic lemniscate `{|Φ₁₄(z)| < C}` is disconnected for `C < 1/15625`.**
Same engine at `ζ₁₄ = exp(πi/7)`.  Coprimality to `14` is what makes the radius
work: the nearest 14th roots of unity (`≈25.7°` away) are NOT primitive; the
nearest primitive ones (`i = 3, 13`) sit at angle gap `2π/7 ≈ 51.4°`. -/
theorem not_isPreconnected_levelSet_fourteen {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 15625) :
    ¬ IsPreconnected {z : ℂ | ‖(cyclotomic 14 ℂ).eval z‖ < C} := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / 14)) 14 :=
    Complex.isPrimitiveRoot_exp 14 (by norm_num)
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 14) with hζdef
  have hζexp : ∀ i : ℕ, ζ ^ i = Complex.exp (↑(2 * Real.pi * i / 14) * Complex.I) := by
    intro i
    rw [hζdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hζ1 : ζ = Complex.exp (↑(2 * Real.pi / 14) * Complex.I) := by
    have h := hζexp 1
    rw [pow_one] at h
    rw [h]
    congr 2
    push_cast
    ring
  have hset : {z : ℂ | ‖(cyclotomic 14 ℂ).eval z‖ < C}
      = {z : ℂ | ‖∏ μ ∈ primitiveRoots 14 ℂ, (z - μ)‖ < C} := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hset]
  have hcard : (primitiveRoots 14 ℂ).card = 6 := by
    rw [Complex.card_primitiveRoots]
    decide
  refine not_isPreconnected_lemniscate (a := ζ) (b := ζ ^ 3) ?_ ?_ ?_ hC
    (by norm_num : (0 : ℝ) ≤ 1 / 5) ?_ ?_
  · exact (mem_primitiveRoots (by norm_num)).mpr hζ
  · exact (mem_primitiveRoots (by norm_num)).mpr
      ((hζ.pow_iff_coprime (by norm_num) 3).mpr (by decide))
  · -- `ζ³ ≠ ζ`
    intro h
    have hne : ζ ≠ 0 := Complex.exp_ne_zero _
    have h2 : ζ ^ 2 = 1 := by
      have h3 : ζ * ζ ^ 2 = ζ * 1 := by
        rw [mul_one, ← pow_succ']
        exact h
      exact mul_left_cancel₀ hne h3
    have : (14 : ℕ) ∣ 2 := hζ.dvd_of_pow_eq_one 2 h2
    omega
  · rw [hcard]
    have : ((1 : ℝ) / 5) ^ 6 = 1 / 15625 := by norm_num
    linarith
  · intro μ hμ hμζ
    haveI : NeZero (14 : ℕ) := ⟨by norm_num⟩
    have hμprim : IsPrimitiveRoot μ 14 := (mem_primitiveRoots (by norm_num)).mp hμ
    obtain ⟨i, hi14, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμprim.pow_eq_one
    have hcop : Nat.Coprime i 14 := (hζ.pow_iff_coprime (by norm_num) i).mp hμprim
    rw [dist_comm, hζexp i, hζ1]
    interval_cases i
    · exact absurd hcop (by decide)
    · exact absurd (pow_one ζ) hμζ
    · exact absurd hcop (by decide)
    · -- `i = 3`, gap `2π/7`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 3 / 14 - 2 * Real.pi / 14 = 2 * Real.pi / 7 by ring]
      linarith [cos_two_pi_div_seven_lt]
    · exact absurd hcop (by decide)
    · -- `i = 5`, gap `4π/7`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 5 / 14 - 2 * Real.pi / 14 = 4 * Real.pi / 7 by ring]
      linarith [cos_four_pi_div_seven_neg]
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- `i = 9`, gap `8π/7`, cosine equals `cos (6π/7)`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 9 / 14 - 2 * Real.pi / 14 = 2 * Real.pi - 6 * Real.pi / 7 by ring,
        Real.cos_two_pi_sub]
      linarith [cos_six_pi_div_seven_neg]
    · exact absurd hcop (by decide)
    · -- `i = 11`, gap `10π/7`, cosine equals `cos (4π/7)`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 11 / 14 - 2 * Real.pi / 14 = 2 * Real.pi - 4 * Real.pi / 7 by ring,
        Real.cos_two_pi_sub]
      linarith [cos_four_pi_div_seven_neg]
    · exact absurd hcop (by decide)
    · -- `i = 13`, gap `12π/7`, cosine equals `cos (2π/7)`
      apply two_fifths_lt_dist_of_cos_lt
      push_cast
      rw [show 2 * Real.pi * 13 / 14 - 2 * Real.pi / 14 = 2 * Real.pi - 2 * Real.pi / 7 by ring,
        Real.cos_two_pi_sub]
      linarith [cos_two_pi_div_seven_lt]

/-- `Φ₁₄` lemniscates are not path-connected in the sub-threshold regime. -/
theorem not_isPathConnected_levelSet_fourteen {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 15625) :
    ¬ IsPathConnected {z : ℂ | ‖(cyclotomic 14 ℂ).eval z‖ < C} :=
  fun h => not_isPreconnected_levelSet_fourteen hC hC' h.isConnected.isPreconnected

/-! ## The uniform sextic capstone -/

/-- **The `φ(n) = 6` layer is CLOSED**: for every `n` with `φ(n) = 6` — i.e.
`n ∈ {7, 9, 14, 18}` — the cyclotomic lemniscate `{z : ‖Φₙ(z)‖ < C}` is
disconnected for every `0 < C < 1/15625` (uniform threshold `(1/5)⁶`). -/
theorem not_isPreconnected_levelSet_sextic {n : ℕ} (hn : n ∈ ({7, 9, 14, 18} : Finset ℕ))
    {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 15625) :
    ¬ IsPreconnected {z : ℂ | ‖(cyclotomic n ℂ).eval z‖ < C} := by
  fin_cases hn
  · exact not_isPreconnected_levelSet_seven hC hC'
  · exact not_isPreconnected_levelSet_nine hC hC'
  · exact not_isPreconnected_levelSet_fourteen hC hC'
  · exact not_isPreconnected_levelSet_eighteen hC hC'

/-- Path-connectivity form of the sextic capstone. -/
theorem not_isPathConnected_levelSet_sextic {n : ℕ} (hn : n ∈ ({7, 9, 14, 18} : Finset ℕ))
    {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 15625) :
    ¬ IsPathConnected {z : ℂ | ‖(cyclotomic n ℂ).eval z‖ < C} :=
  fun h => not_isPreconnected_levelSet_sextic hn hC hC' h.isConnected.isPreconnected

#check @cos_two_pi_div_seven_cubic
#check @cos_two_pi_div_seven_lt
#check @not_isPreconnected_levelSet_seven
#check @not_isPreconnected_levelSet_fourteen
#check @not_isPreconnected_levelSet_sextic
#check @not_isPathConnected_levelSet_sextic

end CyclotomicPolynomialsOQ02OQ15
