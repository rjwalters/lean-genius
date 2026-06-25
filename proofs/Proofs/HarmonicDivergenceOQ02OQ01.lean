/-
Harmonic Divergence, Open Question 02 → 01:
The Bertrand series convergence dichotomy for a *real* exponent.

The parent (OQ-02) treated two isolated cases of the iterated-log series
  Σ_{n≥2} 1 / (n · (log n)^p):
the borderline divergent case p = 1, and the convergent case p = 2.

This file proves the full **threshold theorem** for every real exponent p:

      Σ_{n≥2} 1 / (n · (log n)^p)  converges  ⟺  p > 1.

The exponent is a genuine real number `p : ℝ` (an `rpow` of `Real.log n`),
so the statement interpolates continuously across the entire family and pins
the convergence boundary at p = 1. The parent's two cases (p = 1 divergent,
p = 2 convergent) are recovered as immediate corollaries, and the new content
is the uniform dichotomy — including the delicate strip 0 < p < 1 (divergent)
and the full divergent half-line p ≤ 1 (negative p included).

Proof architecture:
* For p ≥ 0 the term is antitone, so the Cauchy condensation test applies.
  The condensed term at k ≥ 1 is
      2^k / (2^k · (log 2^k)^p) = 1 / (k·log 2)^p = (1/(log 2)^p) · (1/k^p),
  a constant multiple of the real p-series `Σ 1/k^p`, which converges iff p > 1
  (`Real.summable_one_div_nat_rpow`).
* For p < 0 the term dominates the harmonic term 1/n on the tail n ≥ 3
  (there `(log n)^p ≤ 1`), so the series diverges by comparison.

A note on the small-index convention: `log 1 = 0` makes `1/(1·(log 1)^p)`
singular, and the naive `if n < 2 then 0` truncation is *not* antitone at
n = 1 (it dips to 0 below the n = 2 term, breaking the condensation
hypothesis). We instead cap the values at n = 0, 1 to the n = 2 term. This
changes only finitely many terms and therefore leaves convergence — the sole
quantity the theorem speaks about — unchanged, while making the sequence
genuinely non-increasing on all positive indices.

Axiom count: 0
Sorry count: 0
-/

import Mathlib

open Filter Topology

namespace HarmonicDivergenceOQ02OQ01

/-! ## The real-exponent Bertrand term -/

/-- The Bertrand term `1 / (n · (log n)^p)` for `n ≥ 2`, capped at the `n = 2`
value for `n < 2`. The cap is a finite modification (it touches only `n = 0, 1`)
and is chosen so that the sequence is non-increasing on all positive indices,
which the Cauchy condensation test requires. -/
noncomputable def bertrand (p : ℝ) (n : ℕ) : ℝ :=
  if n < 2 then 1 / ((2 : ℝ) * (Real.log 2) ^ p)
           else 1 / ((n : ℝ) * (Real.log n) ^ p)

/-- For `n ≥ 2`, `bertrand p n` is the genuine term `1 / (n · (log n)^p)`. -/
theorem bertrand_of_ge_two (p : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    bertrand p n = 1 / ((n : ℝ) * (Real.log n) ^ p) := by
  unfold bertrand; rw [if_neg (by omega)]

/-- The denominator `n · (log n)^p` is positive for `n ≥ 2`. -/
private theorem denom_pos {n : ℕ} (hn : 2 ≤ n) (p : ℝ) :
    0 < (n : ℝ) * (Real.log n) ^ p := by
  have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  exact mul_pos (by linarith) (Real.rpow_pos_of_pos (Real.log_pos h1) p)

/-- Monotonicity of the denominator for `p ≥ 0`: larger index ⇒ larger
`n · (log n)^p`. -/
private theorem denom_mono (p : ℝ) (hp : 0 ≤ p) {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (a : ℝ) * (Real.log a) ^ p ≤ (b : ℝ) * (Real.log b) ^ p := by
  have ha1 : (1 : ℝ) < (a : ℝ) := by exact_mod_cast (show 1 < a by omega)
  have hlogapos : 0 < Real.log a := Real.log_pos ha1
  apply mul_le_mul
  · exact_mod_cast hab
  · exact Real.rpow_le_rpow (le_of_lt hlogapos)
      (Real.log_le_log (by linarith) (by exact_mod_cast hab)) hp
  · exact Real.rpow_nonneg (le_of_lt hlogapos) p
  · positivity

/-- `bertrand p` is nonnegative everywhere. -/
theorem bertrand_nonneg (p : ℝ) (n : ℕ) : 0 ≤ bertrand p n := by
  unfold bertrand
  split_ifs with h
  · have : 0 < (2 : ℝ) * (Real.log 2) ^ p :=
      mul_pos (by norm_num) (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) p)
    exact le_of_lt (one_div_pos.mpr this)
  · exact le_of_lt (one_div_pos.mpr (denom_pos (by omega) p))

/-- For `p ≥ 0`, `bertrand p` is antitone on the positive integers:
`0 < m ≤ n → bertrand p n ≤ bertrand p m`. -/
theorem bertrand_antitone (p : ℝ) (hp : 0 ≤ p) :
    ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → bertrand p n ≤ bertrand p m := by
  intro m n hm hmn
  have hCval : bertrand p 1 = 1 / ((2 : ℝ) * (Real.log 2) ^ p) := by
    unfold bertrand; rw [if_pos (by omega)]
  by_cases hm2 : m < 2
  · have hm1 : m = 1 := by omega
    subst hm1
    rw [hCval]
    by_cases hn2 : n < 2
    · have : n = 1 := by omega
      subst this; rw [hCval]
    · push_neg at hn2
      rw [bertrand_of_ge_two p hn2]
      have hle : (2 : ℝ) * (Real.log 2) ^ p ≤ (n : ℝ) * (Real.log n) ^ p := by
        have := denom_mono p hp (show (2 : ℕ) ≤ 2 by norm_num) hn2
        simpa using this
      exact one_div_le_one_div_of_le
        (mul_pos (by norm_num) (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) p)) hle
  · push_neg at hm2
    rw [bertrand_of_ge_two p hm2, bertrand_of_ge_two p (le_trans hm2 hmn)]
    exact one_div_le_one_div_of_le (denom_pos hm2 p) (denom_mono p hp hm2 hmn)

/-! ## The condensed term -/

/-- The Cauchy-condensed term at `k ≥ 1`:
`2^k · bertrand p (2^k) = (1/(log 2)^p) · (1/k^p)`. -/
theorem condensed_eq (p : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ k * bertrand p (2 ^ k) =
      (1 / (Real.log 2) ^ p) * (1 / ((k : ℝ) ^ p)) := by
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [bertrand_of_ge_two p h2k]
  have hlog : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hlog, Real.mul_rpow (by positivity) (Real.log_nonneg (by norm_num))]
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have h2 : ((2 ^ k : ℕ) : ℝ) ≠ 0 := by positivity
  have hkp : ((k : ℝ) ^ p) ≠ 0 := (Real.rpow_pos_of_pos hkpos p).ne'
  have hlp : ((Real.log 2) ^ p) ≠ 0 := (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) p).ne'
  push_cast
  field_simp

/-! ## The convergence dichotomy -/

/-- **Bertrand series, nonnegative exponent.** For `p ≥ 0`,
`Σ bertrand p n` converges iff `p > 1`. Proved by Cauchy condensation:
the condensed series is a constant multiple of the real p-series `Σ 1/k^p`. -/
theorem bertrand_summable_iff_of_nonneg (p : ℝ) (hp : 0 ≤ p) :
    Summable (bertrand p) ↔ 1 < p := by
  rw [← summable_condensed_iff_of_nonneg (bertrand_nonneg p) (bertrand_antitone p hp)]
  rw [← summable_nat_add_iff 1]
  have hc : (1 / (Real.log 2) ^ p) ≠ 0 :=
    one_div_ne_zero (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) p).ne'
  have hcong : (fun k : ℕ => (2 : ℝ) ^ (k + 1) * bertrand p (2 ^ (k + 1)))
             = (fun k : ℕ => (1 / (Real.log 2) ^ p) * (1 / (((k + 1 : ℕ) : ℝ) ^ p))) := by
    funext k; exact condensed_eq p (k + 1) (by omega)
  rw [hcong, summable_mul_left_iff hc]
  exact (summable_nat_add_iff 1).trans Real.summable_one_div_nat_rpow

/-- The `p = 0` Bertrand series (essentially the harmonic series) diverges. -/
theorem bertrand_zero_not_summable : ¬ Summable (bertrand 0) := by
  rw [bertrand_summable_iff_of_nonneg 0 le_rfl]; norm_num

/-- **Bertrand series, negative exponent.** For `p < 0` the series diverges,
because on the tail `n ≥ 3` the term dominates the harmonic term `1/n`. -/
theorem bertrand_not_summable_of_neg {p : ℝ} (hp : p < 0) :
    ¬ Summable (bertrand p) := by
  intro hsum
  have h3 : Summable (fun n : ℕ => bertrand p (n + 3)) := (summable_nat_add_iff 3).mpr hsum
  have hle : ∀ n : ℕ, bertrand 0 (n + 3) ≤ bertrand p (n + 3) := by
    intro n
    have hn3 : 2 ≤ n + 3 := by omega
    rw [bertrand_of_ge_two 0 hn3, bertrand_of_ge_two p hn3, Real.rpow_zero]
    apply one_div_le_one_div_of_le (denom_pos hn3 p)
    have hlog1 : (1 : ℝ) ≤ Real.log ((n + 3 : ℕ) : ℝ) := by
      have hy : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by positivity
      rw [Real.le_log_iff_exp_le hy]
      have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have h3le : (3 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by
        push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
      linarith
    have hp1 : (Real.log ((n + 3 : ℕ) : ℝ)) ^ p ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlog1 hp.le
    exact mul_le_mul_of_nonneg_left hp1 (by positivity)
  have h0shift : Summable (fun n : ℕ => bertrand 0 (n + 3)) :=
    Summable.of_nonneg_of_le (fun n => bertrand_nonneg 0 (n + 3)) hle h3
  exact bertrand_zero_not_summable ((summable_nat_add_iff 3).mp h0shift)

/-- **The Bertrand convergence threshold (all real exponents).**

  `Σ_{n} 1 / (n · (log n)^p)` converges  ⟺  `p > 1`. -/
theorem bertrand_summable_iff (p : ℝ) : Summable (bertrand p) ↔ 1 < p := by
  rcases lt_or_ge p 0 with hp | hp
  · constructor
    · intro h; exact absurd h (bertrand_not_summable_of_neg hp)
    · intro h; linarith
  · exact bertrand_summable_iff_of_nonneg p hp

/-! ## Corollaries: recovering the parent's two cases and the full dichotomy -/

/-- For `p ≤ 1` the Bertrand series diverges (includes the borderline `p = 1`
and the entire strip `0 < p < 1`). -/
theorem bertrand_not_summable_of_le_one {p : ℝ} (hp : p ≤ 1) :
    ¬ Summable (bertrand p) := by
  rw [bertrand_summable_iff]; exact not_lt.mpr hp

/-- For `p > 1` the Bertrand series converges. -/
theorem bertrand_summable_of_one_lt {p : ℝ} (hp : 1 < p) :
    Summable (bertrand p) := by
  rw [bertrand_summable_iff]; exact hp

/-- **Parent case p = 1** (borderline): `Σ 1/(n·log n)` diverges. -/
theorem logHarmonic_diverges : ¬ Summable (bertrand 1) :=
  bertrand_not_summable_of_le_one le_rfl

/-- **Parent case p = 2**: `Σ 1/(n·(log n)²)` converges. -/
theorem logHarmonicSq_converges : Summable (bertrand 2) :=
  bertrand_summable_of_one_lt (by norm_num)

end HarmonicDivergenceOQ02OQ01
