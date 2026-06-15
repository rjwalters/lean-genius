/-
# Irrationality of √2 + √3 + √5 + √7 (OQ-01 of `sqrt2-plus-sqrt3-plus-sqrt5-irrational`)

## Strategy D — algebraic integer in a bounded interval

Let `α := √2 + √3 + √5 + √7`. This proof sidesteps the entire degree-16
minimal-polynomial / iterated-squaring machinery (Strategies A–C) via a short
integral-closure descent:

1. Each `√k` (k ∈ {2,3,5,7}) is a root of the monic integer polynomial
   `X² − C k`, hence `IsIntegral ℤ (√k)`. Algebraic integers are closed under
   addition (`IsIntegral.add`), so `α` is integral over `ℤ`.
2. Suppose `α` were rational, `α = (q : ℝ)` with `q : ℚ`. Integrality descends
   along the injective `algebraMap ℚ ℝ` (`isIntegral_algebraMap_iff`), giving
   `IsIntegral ℤ q`.
3. `ℤ` is integrally closed in its fraction field `ℚ`
   (`IsIntegrallyClosed.isIntegral_iff`), so `q = (n : ℤ)` for some integer `n`;
   hence `α = (n : ℝ)`.
4. But `8 < α < 9` (α ≈ 8.0281), so no integer can equal `α`. Contradiction,
   so `α` is irrational. ∎

This avoids surd isolation, the degree-16 minimal polynomial, and any new
Mathlib theory — only the standard integral-closure API plus four `norm_num`
radical bounds.

## Provenance

Bearer-confirmed at Mathlib pin `v4.26.0` over four build-free sessions; the
load-bearing arithmetic (integrality of each `√k`, the bound `8 < α < 9`) is
reproduced by `research/problems/.../verify_strategy_d.py`.

## Status
- [x] `isIntegral_sqrt_natCast` — √(k:ℕ) is integral over ℤ (root of monic X²−C k)
- [x] `alpha_isIntegral`        — α is integral over ℤ (three `IsIntegral.add`)
- [x] `sqrt_bounds`             — generic rational bracket lo < √x < hi from lo²<x<hi²
- [x] `alpha_gt_eight`, `alpha_lt_nine` — `8 < α < 9` via the rational witnesses
- [x] `irrational_sqrt2_plus_sqrt3_plus_sqrt5_plus_sqrt7` — main theorem
-/

import Mathlib

set_option maxHeartbeats 400000

open Polynomial

namespace Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01

noncomputable section

/-- `√(k : ℕ)` is an algebraic integer: it is a root of the monic integer
polynomial `X² − C k`. -/
theorem isIntegral_sqrt_natCast (k : ℕ) : IsIntegral ℤ (Real.sqrt (k : ℝ)) := by
  refine ⟨X ^ 2 - C (k : ℤ), monic_X_pow_sub_C (k : ℤ) (by norm_num), ?_⟩
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  -- The `IsIntegral` witness goal is an `eval₂` (via `RingHom.IsIntegralElem`);
  -- include both `eval₂_*` and `aeval_*`/`map_*` rewrites so this is robust to
  -- whichever normal form the goal is presented in.
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_sub, map_pow, aeval_X,
    aeval_C, algebraMap_int_eq, eq_intCast, Int.cast_natCast]
  rw [Real.sq_sqrt hk]
  ring

/-- `α = √2 + √3 + √5 + √7` is integral over `ℤ` (sum of four algebraic
integers). -/
theorem alpha_isIntegral :
    IsIntegral ℤ (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 + Real.sqrt 7) := by
  have h2 : IsIntegral ℤ (Real.sqrt 2) := by simpa using isIntegral_sqrt_natCast 2
  have h3 : IsIntegral ℤ (Real.sqrt 3) := by simpa using isIntegral_sqrt_natCast 3
  have h5 : IsIntegral ℤ (Real.sqrt 5) := by simpa using isIntegral_sqrt_natCast 5
  have h7 : IsIntegral ℤ (Real.sqrt 7) := by simpa using isIntegral_sqrt_natCast 7
  exact ((h2.add h3).add h5).add h7

/-- Generic rational bracket: a positive `lo` with `lo² < x` and a positive `hi`
with `x < hi²` sandwich `√x`. Used to pin `8 < α < 9` from rational witnesses. -/
theorem sqrt_bounds (x lo hi : ℝ) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (h1 : lo ^ 2 < x) (h2 : x < hi ^ 2) :
    lo < Real.sqrt x ∧ Real.sqrt x < hi := by
  have hx : 0 ≤ x := le_of_lt (lt_of_le_of_lt (sq_nonneg lo) h1)
  refine ⟨?_, ?_⟩
  · calc lo = Real.sqrt (lo ^ 2) := (Real.sqrt_sq hlo).symm
      _ < Real.sqrt x := Real.sqrt_lt_sqrt (sq_nonneg lo) h1
  · calc Real.sqrt x < Real.sqrt (hi ^ 2) := Real.sqrt_lt_sqrt hx h2
      _ = hi := Real.sqrt_sq hhi

/-- Lower bound: `8 < √2 + √3 + √5 + √7`. Witnesses
`√2 > 1.41, √3 > 1.73, √5 > 2.23, √7 > 2.64` sum to `8.01 > 8`. -/
theorem alpha_gt_eight :
    (8 : ℝ) < Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 + Real.sqrt 7 := by
  obtain ⟨l2, _⟩ := sqrt_bounds 2 1.41 1.42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨l3, _⟩ := sqrt_bounds 3 1.73 1.74 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨l5, _⟩ := sqrt_bounds 5 2.23 2.24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨l7, _⟩ := sqrt_bounds 7 2.64 2.65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Upper bound: `√2 + √3 + √5 + √7 < 9`. Witnesses
`√2 < 1.42, √3 < 1.74, √5 < 2.24, √7 < 2.65` sum to `8.05 < 9`. -/
theorem alpha_lt_nine :
    Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 + Real.sqrt 7 < (9 : ℝ) := by
  obtain ⟨_, u2⟩ := sqrt_bounds 2 1.41 1.42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, u3⟩ := sqrt_bounds 3 1.73 1.74 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, u5⟩ := sqrt_bounds 5 2.23 2.24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨_, u7⟩ := sqrt_bounds 7 2.64 2.65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- **Main theorem**: `√2 + √3 + √5 + √7` is irrational. -/
theorem irrational_sqrt2_plus_sqrt3_plus_sqrt5_plus_sqrt7 :
    Irrational (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 + Real.sqrt 7) := by
  rintro ⟨q, hq⟩
  -- hq : (q : ℝ) = √2 + √3 + √5 + √7
  -- Step 1–2: α integral over ℤ; descend to q integral over ℤ.
  have hα := alpha_isIntegral
  have hq_int : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (algebraMap ℚ ℝ).injective]
    have hmap : (algebraMap ℚ ℝ) q
        = Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 + Real.sqrt 7 := by
      rw [eq_ratCast]; exact hq
    rw [hmap]; exact hα
  -- Step 3: ℤ integrally closed in ℚ ⇒ q is an integer.
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq_int
  -- hn : algebraMap ℤ ℚ n = q
  have hqn : q = (n : ℚ) := hn.symm.trans (eq_intCast (algebraMap ℤ ℚ) n)
  have hαn : Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 + Real.sqrt 7 = (n : ℝ) := by
    rw [← hq, hqn]; push_cast; ring
  -- Step 4: but 8 < α < 9, so no integer equals α.
  have hlb := alpha_gt_eight
  have hub := alpha_lt_nine
  rw [hαn] at hlb hub
  have h8 : (8 : ℤ) < n := by exact_mod_cast hlb
  have h9 : n < (9 : ℤ) := by exact_mod_cast hub
  omega

end

end Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01
