/-
# Erdős Problem #396 — OQ-04 → OQ-01 → OQ-01 → OQ-02 → OQ-02 → OQ-02: explicit constants in the `1/2` exponent, bracketing the Wallis constant `1/√π`

The parent entry `Erdos396OQ04OQ01OQ01OQ02OQ02` extracts the `1/2` critical
exponent of the central binomial coefficient `C(2n,n)` from its two-term
recurrence: normalising each step by the limiting rate `4` and applying
`log y ≤ y − 1` telescopes to `C(2n,n)/4^n ≤ exp(−(1/2)·H_n) ∼ n^{−1/2}`,
with a matching reciprocal lower bracket of the same `1/2` order.  Both brackets
were *order* statements — they pinned the exponent `1/2` but left the leading
constant in `C(2n,n) ∼ 4^n/√(π n)` (the analytic Wallis/Stirling number `1/√π`)
unaddressed.

That entry's first closing open question asked:

> Can one extract **explicit constants** `c₁, c₂` with
> `c₁·4^n/√n ≤ C(2n,n) ≤ c₂·4^n/√n` directly from the recurrence, isolating
> the `√π` constant as the only ingredient genuinely requiring an analytic input?

This file answers it affirmatively with completely elementary constants, no
Stirling and no Wallis limit.  The engine is two **squared** integer bounds,
each a one-line induction over the recurrence:

  **`centralBinom_sq_lower`** : `16^n ≤ 4·n·C(2n,n)^2`   (for `n ≥ 1`),
  **`centralBinom_sq_upper`** : `(3n+1)·C(2n,n)^2 ≤ 16^n` (for all `n`).

Writing `a_n = C(2n,n)/4^n` and `16^n = (4^n)^2`, these say
`(2√n·a_n)^2 ≥ 1` and `(√(3n+1)·a_n)^2 ≤ 1`; taking square roots gives the
explicit two-sided bound

  **`centralBinom_bracket`** : `(1/2)·4^n/√n ≤ C(2n,n) ≤ (1/√3)·4^n/√n`
  (for `n ≥ 1`),

so `c₁ = 1/2` and `c₂ = 1/√3` work.  The squared recurrence step is the pair of
elementary polynomial identities

  `16·(3n+1)·(n+1)^2 − 4·(3n+4)·(2n+1)^2 = 4n ≥ 0`   (upper step),
  `(2n+1)^2 − 4n·(n+1) = 1 ≥ 0`                       (lower step),

which are exactly the deficits driving the harmonic telescoping of the parent.

Finally **`wallis_constant_bracketed`** records that the *true* constant `1/√π`
of `C(2n,n) ∼ 4^n/√(π n)` lies strictly between the two elementary constants:

  `1/2 < 1/√π < 1/√3`,

equivalent to `3 < π < 4`.  Thus the recurrence alone brackets the asymptotic
constant inside `(1/2, 1/√3)`; pinning it to the single value `1/√π` is the
*only* step that genuinely needs an analytic (Wallis/Stirling) input — precisely
the dichotomy the open question anticipated.

All theorems are fully machine-checked with no axioms or sorries.
-/

import Mathlib

open Nat Finset

namespace Erdos396OQ04OQ01OQ01OQ02OQ02OQ02

/-! ## The recurrence over `ℝ`

Mathlib's `Nat.succ_mul_centralBinom_succ` reads `(n+1)·C(2(n+1),n+1) =
2·(2n+1)·C(2n,n)`.  We cast it to `ℝ` once and square it; everything below is
driven by this single identity. -/

/-- The central-binomial recurrence over `ℝ`:
    `(n+1)·C(2(n+1),n+1) = 2·(2n+1)·C(2n,n)`. -/
theorem cb_rec (n : ℕ) :
    ((n : ℝ) + 1) * (centralBinom (n + 1) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * (centralBinom n : ℝ) := by
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.succ_mul_centralBinom_succ n)
  push_cast at h
  linarith [h]

/-- The **squared** recurrence, the only form used in the inductions:
    `(n+1)^2·C(2(n+1),n+1)^2 = 4·(2n+1)^2·C(2n,n)^2`. -/
theorem cb_rec_sq (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 * (centralBinom (n + 1) : ℝ) ^ 2
      = 4 * (2 * (n : ℝ) + 1) ^ 2 * (centralBinom n : ℝ) ^ 2 := by
  have e : (((n : ℝ) + 1) * (centralBinom (n + 1) : ℝ)) ^ 2
      = (2 * (2 * (n : ℝ) + 1) * (centralBinom n : ℝ)) ^ 2 := by
    rw [cb_rec]
  linear_combination e

/-! ## The two squared integer bounds -/

/-- **Upper squared bound.** `(3n+1)·C(2n,n)^2 ≤ 16^n` for every `n`.
    The induction step is the polynomial identity
    `16·(3n+1)·(n+1)^2 − 4·(3n+4)·(2n+1)^2 = 4n ≥ 0`. -/
theorem centralBinom_sq_upper (n : ℕ) :
    (3 * (n : ℝ) + 1) * (centralBinom n : ℝ) ^ 2 ≤ 16 ^ n := by
  induction n with
  | zero => simp [Nat.centralBinom_zero]
  | succ n ih =>
    push_cast
    set x : ℝ := (centralBinom n : ℝ) with hx
    set y : ℝ := (centralBinom (n + 1) : ℝ) with hy
    have hN1 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    have hpow : (16 : ℝ) ^ (n + 1) = 16 * 16 ^ n := by rw [pow_succ]; ring
    -- IH multiplied by the positive factor `16·(n+1)^2`
    have ih' : 16 * ((n : ℝ) + 1) ^ 2 * ((3 * (n : ℝ) + 1) * x ^ 2)
        ≤ 16 * ((n : ℝ) + 1) ^ 2 * 16 ^ n :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    -- the squared recurrence, pre-multiplied by the step's linear factor `(3n+4)`
    have hkey : (3 * (n : ℝ) + 4) * (((n : ℝ) + 1) ^ 2 * y ^ 2)
        = (3 * (n : ℝ) + 4) * (4 * (2 * (n : ℝ) + 1) ^ 2 * x ^ 2) := by
      rw [cb_rec_sq n]
    -- target multiplied through by `(n+1)^2`
    have hmul : (3 * ((n : ℝ) + 1) + 1) * y ^ 2 * ((n : ℝ) + 1) ^ 2
        ≤ 16 ^ (n + 1) * ((n : ℝ) + 1) ^ 2 := by
      rw [hpow]
      nlinarith [ih', hkey, mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)]
    exact le_of_mul_le_mul_right hmul hN1

/-- **Lower squared bound.** `16^n ≤ 4·n·C(2n,n)^2` for every `n ≥ 1`.
    The induction step is the polynomial identity
    `(2n+1)^2 − 4n·(n+1) = 1 ≥ 0`.  (The bound fails at `n = 0`, where the
    right-hand side is `0`.) -/
theorem centralBinom_sq_lower (n : ℕ) (hn : 1 ≤ n) :
    (16 : ℝ) ^ n ≤ 4 * (n : ℝ) * (centralBinom n : ℝ) ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h1 : centralBinom 1 = 2 := by decide
    rw [h1]; norm_num
  | succ n hn ih =>
    push_cast
    set x : ℝ := (centralBinom n : ℝ) with hx
    set y : ℝ := (centralBinom (n + 1) : ℝ) with hy
    have hN1 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    have hpow : (16 : ℝ) ^ (n + 1) = 16 * 16 ^ n := by rw [pow_succ]; ring
    have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    -- IH multiplied by the positive factor `16·(n+1)^2`
    have ih' : 16 * ((n : ℝ) + 1) ^ 2 * 16 ^ n
        ≤ 16 * ((n : ℝ) + 1) ^ 2 * (4 * (n : ℝ) * x ^ 2) :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    -- the squared recurrence, pre-multiplied by the step's linear factor `4(n+1)`
    have hkey : (4 * ((n : ℝ) + 1)) * (((n : ℝ) + 1) ^ 2 * y ^ 2)
        = (4 * ((n : ℝ) + 1)) * (4 * (2 * (n : ℝ) + 1) ^ 2 * x ^ 2) := by
      rw [cb_rec_sq n]
    have hmul : (16 : ℝ) ^ (n + 1) * ((n : ℝ) + 1) ^ 2
        ≤ 4 * ((n : ℝ) + 1) * y ^ 2 * ((n : ℝ) + 1) ^ 2 := by
      rw [hpow]
      nlinarith [ih', hkey, mul_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1) (sq_nonneg x)]
    exact le_of_mul_le_mul_right hmul hN1

/-! ## The explicit real bracket

Square roots of the two bounds give the explicit constants `1/2` and `1/√3`. -/

/-- Positivity of `C(2n,n)` over `ℝ`. -/
theorem cb_pos (n : ℕ) : (0 : ℝ) < (centralBinom n : ℝ) := by
  exact_mod_cast Nat.centralBinom_pos n

/-- `16^n = 4^n · 4^n` over `ℝ`. -/
theorem pow16_eq (n : ℕ) : (16 : ℝ) ^ n = 4 ^ n * 4 ^ n := by
  rw [show (16 : ℝ) = 4 * 4 by norm_num, mul_pow]

/-- **Explicit lower constant `1/2`.** For `n ≥ 1`, `(1/2)·4^n/√n ≤ C(2n,n)`. -/
theorem centralBinom_lower_const (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2) * 4 ^ n / Real.sqrt n ≤ (centralBinom n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsn : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  rw [div_le_iff₀ hsqrt]
  -- reduces to `(1/2)·4^n ≤ C·√n`; both sides positive, so compare squares
  have hcsn : ((centralBinom n : ℝ) * Real.sqrt n) ^ 2
      = (centralBinom n : ℝ) ^ 2 * (n : ℝ) := by rw [mul_pow, hsn]
  have hsq : (1 / 2 * 4 ^ n) ^ 2 ≤ ((centralBinom n : ℝ) * Real.sqrt n) ^ 2 := by
    rw [hcsn]
    nlinarith [centralBinom_sq_lower n hn, pow16_eq n]
  have hlpos : (0 : ℝ) < 1 / 2 * 4 ^ n := by positivity
  have hrpos : (0 : ℝ) ≤ (centralBinom n : ℝ) * Real.sqrt n := by positivity
  have hsum : (0 : ℝ) < 1 / 2 * 4 ^ n + (centralBinom n : ℝ) * Real.sqrt n :=
    add_pos_of_pos_of_nonneg hlpos hrpos
  nlinarith [hsq, hsum]

/-- **Explicit upper constant `1/√3`.** For `n ≥ 1`, `C(2n,n) ≤ (1/√3)·4^n/√n`.
    (Sharper still — the squared bound gives `C(2n,n) ≤ 4^n/√(3n+1)`.) -/
theorem centralBinom_upper_const (n : ℕ) (hn : 1 ≤ n) :
    (centralBinom n : ℝ) ≤ (1 / Real.sqrt 3) * 4 ^ n / Real.sqrt n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrtn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsqrt3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsn : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hs3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [le_div_iff₀ hsqrtn]
  -- reduces to `C·√n ≤ (1/√3)·4^n`; both sides ≥ 0, so compare squares
  have hcsn : ((centralBinom n : ℝ) * Real.sqrt n) ^ 2
      = (centralBinom n : ℝ) ^ 2 * (n : ℝ) := by rw [mul_pow, hsn]
  have hrhs2 : (1 / Real.sqrt 3 * 4 ^ n) ^ 2 = (1 / 3) * (4 ^ n * 4 ^ n) := by
    rw [mul_pow, div_pow, one_pow, hs3]; ring
  have hsq : ((centralBinom n : ℝ) * Real.sqrt n) ^ 2 ≤ (1 / Real.sqrt 3 * 4 ^ n) ^ 2 := by
    rw [hcsn, hrhs2]
    nlinarith [centralBinom_sq_upper n, pow16_eq n,
      mul_nonneg hnpos.le (sq_nonneg (centralBinom n : ℝ)), sq_nonneg (centralBinom n : ℝ)]
  have hlpos : (0 : ℝ) ≤ (centralBinom n : ℝ) * Real.sqrt n := by positivity
  have hrpos : (0 : ℝ) < 1 / Real.sqrt 3 * 4 ^ n := by positivity
  have hsum : (0 : ℝ) < (centralBinom n : ℝ) * Real.sqrt n + 1 / Real.sqrt 3 * 4 ^ n :=
    add_pos_of_nonneg_of_pos hlpos hrpos
  nlinarith [hsq, hsum]

/-- **The explicit two-sided bracket.** For `n ≥ 1`,
    `(1/2)·4^n/√n ≤ C(2n,n) ≤ (1/√3)·4^n/√n`, with the elementary constants
    `c₁ = 1/2` and `c₂ = 1/√3` produced directly from the recurrence. -/
theorem centralBinom_bracket (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2) * 4 ^ n / Real.sqrt n ≤ (centralBinom n : ℝ)
      ∧ (centralBinom n : ℝ) ≤ (1 / Real.sqrt 3) * 4 ^ n / Real.sqrt n :=
  ⟨centralBinom_lower_const n hn, centralBinom_upper_const n hn⟩

/-! ## The true constant `1/√π` is bracketed by the elementary constants

`C(2n,n) ∼ 4^n/√(π n)`, so the genuine leading constant is `1/√π`.  The
recurrence-derived bracket `(1/2, 1/√3)` contains it — and that containment is
exactly `3 < π < 4`. -/

/-- `√4 = 2`. -/
private theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

/-- `1/2 < 1/√π`, equivalently `√π < 2`, equivalently `π < 4`. -/
theorem half_lt_inv_sqrt_pi : (1 : ℝ) / 2 < 1 / Real.sqrt Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsqrt : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hlt : Real.sqrt Real.pi < 2 := by
    rw [← sqrt_four]
    exact Real.sqrt_lt_sqrt hpi.le (by linarith [Real.pi_lt_four])
  exact one_div_lt_one_div_of_lt hsqrt hlt

/-- `1/√π < 1/√3`, equivalently `√3 < √π`, equivalently `3 < π`. -/
theorem inv_sqrt_pi_lt_inv_sqrt_three : 1 / Real.sqrt Real.pi < 1 / Real.sqrt 3 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsqrt3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : Real.sqrt 3 < Real.sqrt Real.pi :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith [Real.pi_gt_three])
  exact one_div_lt_one_div_of_lt hsqrt3 hlt

/-- **The Wallis/Stirling constant is bracketed.** The elementary constants
    `1/2` and `1/√3` produced by the recurrence sandwich the true leading
    constant `1/√π` of `C(2n,n) ∼ 4^n/√(π n)`:

      `1/2 < 1/√π < 1/√3`.

    Equivalently `3 < π < 4`.  Hence the recurrence pins the asymptotic constant
    to the open interval `(1/2, 1/√3)`; identifying it as exactly `1/√π` is the
    single step that requires an analytic (Wallis/Stirling) input. -/
theorem wallis_constant_bracketed :
    (1 : ℝ) / 2 < 1 / Real.sqrt Real.pi ∧ 1 / Real.sqrt Real.pi < 1 / Real.sqrt 3 :=
  ⟨half_lt_inv_sqrt_pi, inv_sqrt_pi_lt_inv_sqrt_three⟩

end Erdos396OQ04OQ01OQ01OQ02OQ02OQ02
