/-
Harmonic Divergence, Open Question 02:
Divergence rate of Σ 1/(n·log n) analogous to H_n ~ ln n.

The harmonic series Σ 1/n diverges at rate H_n ~ log(n).
The "log-harmonic" series Σ_{n≥2} 1/(n·log n) also diverges, but slower:
its partial sums grow like log(log N).

Main results:
1. Σ 1/(n·log n) diverges (via Cauchy condensation test)
2. The condensed series Σ 1/(k·log 2) is a rescaled harmonic series
3. Σ 1/(n·(log n)²) is summable: squaring the log denominator turns the
   divergent borderline case into a convergent series. Same condensation
   framework, condensed series Σ 1/(k²·(log 2)²) is a Basel-rescaled
   p-series with p = 2.

The divergence follows from the Cauchy condensation test (OQ-04):
  2^k · f(2^k) = 2^k / (2^k · k·log 2) = 1/(k·log 2)
  This is (1/log 2) · Σ 1/k, which diverges.

The convergence of the squared-log variant uses the same condensation:
  2^k · g(2^k) = 2^k / (2^k · (k·log 2)²) = 1/(k²·(log 2)²)
  This is (1/(log 2)²) · Σ 1/k², which converges (Basel).

Axiom count: 0
Sorry count: 0
-/

import Mathlib

open Finset Filter BigOperators Topology Real

namespace HarmonicDivergenceOQ02

/-! ## The Log-Harmonic Series: 1/(n · log n)

We define f(n) = 1/(n · log n) for n ≥ 2 and show it diverges using
the Cauchy condensation test. -/

/-- The log-harmonic term: 1/(n · log n) for n ≥ 2, else 0. -/
noncomputable def logHarmonic (n : ℕ) : ℝ :=
  if n < 2 then 0 else 1 / ((n : ℝ) * Real.log n)

/-- logHarmonic is nonneg for all n. -/
theorem logHarmonic_nonneg (n : ℕ) : 0 ≤ logHarmonic n := by
  unfold logHarmonic
  split_ifs with h
  · exact le_refl _
  · apply div_nonneg (le_of_lt one_pos)
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))

/-- For n ≥ 2, logHarmonic n = 1/(n · log n). -/
theorem logHarmonic_of_ge_two {n : ℕ} (hn : 2 ≤ n) :
    logHarmonic n = 1 / ((n : ℝ) * Real.log n) := by
  unfold logHarmonic; simp [show ¬(n < 2) by omega]

/-- n · log n is positive for n ≥ 2. -/
private theorem mul_log_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < (n : ℝ) * Real.log n :=
  mul_pos (by exact_mod_cast (show 0 < n by omega))
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))

/-- logHarmonic is antitone for positive n:
    0 < m ≤ n → logHarmonic n ≤ logHarmonic m. -/
-- NOTE (v4.31 fix, #38611 candidate): the original statement quantified over `0 < m`,
-- which is FALSE — `logHarmonic 1 = 0` (junk value from `1 < 2`) while `logHarmonic 2 > 0`,
-- so `logHarmonic n ≤ logHarmonic 1` fails at n = 2. The `m = 1` case exploited unsound
-- elaboration of `mul_log_pos (by omega)` against an unassigned implicit metavariable on
-- v4.26; v4.31's stricter elaboration order surfaces the (unprovable) real goal. Fixed to
-- the genuinely-true statement `2 ≤ m`, and downstream usage switched to the "eventually"
-- Cauchy condensation variant, which only needs antitone-ness from some point on.
theorem logHarmonic_antitone :
    ∀ ⦃m n : ℕ⦄, 2 ≤ m → m ≤ n → logHarmonic n ≤ logHarmonic m := by
  intro m n hm hmn
  -- m ≥ 2, n ≥ 2: compare 1/(n·log n) ≤ 1/(m·log m)
  rw [logHarmonic_of_ge_two hm, logHarmonic_of_ge_two (le_trans hm hmn)]
  rw [div_le_div_iff₀ (mul_log_pos (le_trans hm hmn)) (mul_log_pos hm)]
  simp only [one_mul]
  -- Need: m · log m ≤ n · log n
  apply mul_le_mul
  · exact_mod_cast hmn
  · exact Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hmn)
  · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  · exact Nat.cast_nonneg _

/-! ## Divergence via Cauchy Condensation

The condensed series: 2^k · logHarmonic(2^k) = 2^k / (2^k · k·log 2) = 1/(k·log 2).
This is (1/log 2) times the harmonic series, which diverges. -/

/-- The condensed logHarmonic at k ≥ 1 equals 1/(k · log 2). -/
theorem condensed_logHarmonic_eq (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ k * logHarmonic (2 ^ k) = 1 / ((k : ℝ) * Real.log 2) := by
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  rw [logHarmonic_of_ge_two h2k]
  have h_log_pow : Real.log (((2 ^ k : ℕ) : ℝ)) = k * Real.log 2 := by
    push_cast
    exact Real.log_pow 2 k
  rw [h_log_pow]
  have hk_pos : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hlog2_pos : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have h2k_pos : (↑(2 ^ k) : ℝ) ≠ 0 := by exact_mod_cast (show 2 ^ k ≠ 0 by positivity)
  field_simp
  push_cast
  ring

/-- The condensed logHarmonic series is not summable.
    It equals 1/(k·log 2) for k ≥ 1, which is a rescaled harmonic series. -/
theorem condensed_logHarmonic_not_summable :
    ¬Summable (fun k : ℕ => (2 : ℝ) ^ k * logHarmonic (2 ^ k)) := by
  -- The condensed series for k ≥ 1 is 1/(k·log 2) = (1/log 2)·(1/k)
  -- Since Σ 1/k diverges, so does (1/log 2)·Σ 1/k
  rw [show (fun k : ℕ => (2 : ℝ) ^ k * logHarmonic (2 ^ k)) =
      (fun k : ℕ => if k = 0 then (2 : ℝ) ^ 0 * logHarmonic (2 ^ 0)
                else 1 / ((k : ℝ) * Real.log 2)) from by
    ext k; by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, condensed_logHarmonic_eq k (by omega)]
  ]
  -- Shift by one (via `summable_nat_add_iff`) to sidestep the k = 0 special case,
  -- then relate the tail to the (divergent) harmonic series 1/(n+1).
  rw [← summable_nat_add_iff 1]
  intro hsum
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have h1 : Summable (fun n : ℕ => Real.log 2 *
      (if n + 1 = 0 then (2 : ℝ) ^ 0 * logHarmonic (2 ^ 0)
        else 1 / (((n + 1 : ℕ) : ℝ) * Real.log 2))) := hsum.mul_left _
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ)) : ℝ)) := by
    refine h1.congr (fun n => ?_)
    rw [if_neg (show n + 1 ≠ 0 by omega)]
    have hn1_ne : (((n + 1 : ℕ)) : ℝ) ≠ 0 := by positivity
    field_simp
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) 1).mp h2)

/-- **The log-harmonic series Σ 1/(n·log n) diverges.**

    Proved via the Cauchy condensation test:
    the condensed series Σ 2^k/(2^k · k·log 2) = Σ 1/(k·log 2)
    is a rescaled harmonic series, which diverges. -/
theorem logHarmonic_not_summable : ¬Summable logHarmonic := by
  rw [← summable_condensed_iff_of_eventually_nonneg
      (Filter.Eventually.of_forall logHarmonic_nonneg)
      (by filter_upwards [Filter.eventually_ge_atTop 2] with k hk
          exact logHarmonic_antitone hk (Nat.le_succ k))]
  exact condensed_logHarmonic_not_summable

/-! ## Connection to the Divergence Rate

The partial sums of Σ_{n≥2} 1/(n·log n) grow like log(log N).
More precisely: Σ_{n=2}^N 1/(n·log n) ~ log(log N) as N → ∞.

This follows from integral comparison:
∫₂ᴺ dx/(x·log x) = log(log N) - log(log 2)

The partial sums and the integral differ by a bounded amount (similar
to how H_N and log N differ by the Euler-Mascheroni constant γ).
-/

/-! ## The Squared-Log Series: 1/(n · (log n)²)

Squaring the log denominator turns divergence into convergence:
Σ_{n≥2} 1/(n·(log n)²) is summable. The proof reuses the same Cauchy
condensation framework as the divergence side; the condensed series
becomes Σ_{k≥1} 1/(k²·(log 2)²), a constant multiple of the convergent
Basel `p`-series with `p = 2`.

This is the next case of the iterated-log convergence hierarchy:
- p < 1:    Σ 1/(n·(log n)^p) diverges
- p = 1:    Σ 1/(n·log n) diverges (above)
- p > 1:    Σ 1/(n·(log n)^p) converges (this section, p = 2 case)
-/

/-- The squared-log term: 1/(n · (log n)²) for n ≥ 2, else 0. -/
noncomputable def logHarmonicSq (n : ℕ) : ℝ :=
  if n < 2 then 0 else 1 / ((n : ℝ) * (Real.log n) ^ 2)

/-- logHarmonicSq is nonneg for all n. -/
theorem logHarmonicSq_nonneg (n : ℕ) : 0 ≤ logHarmonicSq n := by
  unfold logHarmonicSq
  split_ifs with h
  · exact le_refl _
  · apply div_nonneg (le_of_lt one_pos)
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- For n ≥ 2, logHarmonicSq n = 1 / (n · (log n)²). -/
theorem logHarmonicSq_of_ge_two {n : ℕ} (hn : 2 ≤ n) :
    logHarmonicSq n = 1 / ((n : ℝ) * (Real.log n) ^ 2) := by
  unfold logHarmonicSq; simp [show ¬(n < 2) by omega]

/-- n · (log n)² is positive for n ≥ 2. -/
private theorem mul_log_sq_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < (n : ℝ) * (Real.log n) ^ 2 := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog_pos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  exact mul_pos hn_pos (pow_pos hlog_pos 2)

-- NOTE (v4.31 fix, #38611 candidate): same edge-case issue as `logHarmonic_antitone` above
-- — `logHarmonicSq 1 = 0` but `logHarmonicSq 2 > 0`, so `0 < m` was never actually true.
-- Fixed to the genuinely-true `2 ≤ m` statement; see `logHarmonic_antitone` for details.
theorem logHarmonicSq_antitone :
    ∀ ⦃m n : ℕ⦄, 2 ≤ m → m ≤ n → logHarmonicSq n ≤ logHarmonicSq m := by
  intro m n hm hmn
  -- m, n ≥ 2: compare 1/(n·(log n)²) ≤ 1/(m·(log m)²)
  rw [logHarmonicSq_of_ge_two hm, logHarmonicSq_of_ge_two (le_trans hm hmn)]
  rw [div_le_div_iff₀ (mul_log_sq_pos (le_trans hm hmn)) (mul_log_sq_pos hm)]
  simp only [one_mul]
  -- Need: m · (log m)² ≤ n · (log n)²
  have hlog_le : Real.log m ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast (show 0 < m by omega))
      (by exact_mod_cast hmn)
  have hlog_m_nonneg : 0 ≤ Real.log m :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  apply mul_le_mul
  · exact_mod_cast hmn
  · exact pow_le_pow_left₀ hlog_m_nonneg hlog_le 2
  · exact sq_nonneg _
  · exact Nat.cast_nonneg _

/-- The condensed logHarmonicSq at k ≥ 1 equals 1 / (k² · (log 2)²). -/
theorem condensed_logHarmonicSq_eq (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ k * logHarmonicSq (2 ^ k) = 1 / ((k : ℝ) ^ 2 * (Real.log 2) ^ 2) := by
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  rw [logHarmonicSq_of_ge_two h2k]
  have h_log_pow : Real.log (((2 ^ k : ℕ) : ℝ)) = k * Real.log 2 := by
    push_cast
    exact Real.log_pow 2 k
  rw [h_log_pow]
  have hk_pos : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hlog2_pos : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have h2k_pos : (↑(2 ^ k) : ℝ) ≠ 0 := by exact_mod_cast (show 2 ^ k ≠ 0 by positivity)
  field_simp
  push_cast
  ring

/-- The condensed logHarmonicSq series is summable.
    For k ≥ 1, the term equals 1/(k²·(log 2)²) = (1/(log 2)²) · (1/k²),
    a constant multiple of the convergent Basel p-series (p = 2). -/
theorem condensed_logHarmonicSq_summable :
    Summable (fun k : ℕ => (2 : ℝ) ^ k * logHarmonicSq (2 ^ k)) := by
  -- The k = 0 term is 2^0 · logHarmonicSq 1 = 1 · 0 = 0; tail (k ≥ 1) carries
  -- the content. Use summable_nat_add_iff to shift, identify with Basel p-series.
  rw [← summable_nat_add_iff 1]
  -- Goal: Summable (fun k => 2^(k+1) · logHarmonicSq(2^(k+1)))
  have h_basel : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have h_shift : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ) ^ 2)) 1).mpr h_basel
  have h_const :
      Summable (fun k : ℕ => (1 / (Real.log 2) ^ 2) * (1 / (((k + 1 : ℕ) : ℝ) ^ 2)) ) :=
    h_shift.mul_left _
  refine h_const.congr (fun k => ?_)
  -- Show: (1/(log 2)²) · (1/((k+1)²)) = 2^(k+1) · logHarmonicSq(2^(k+1))
  rw [condensed_logHarmonicSq_eq (k + 1) (by omega)]
  push_cast
  have hk1_ne : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have hk1_sq_ne : (((k + 1 : ℕ) : ℝ)) ^ 2 ≠ 0 := pow_ne_zero _ hk1_ne
  have hlog2_pos : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hlog2_sq_ne : (Real.log 2) ^ 2 ≠ 0 := pow_ne_zero _ hlog2_pos
  field_simp

/-- **The squared-log series Σ 1/(n·(log n)²) is summable.**

    Proved via the Cauchy condensation test:
    the condensed series Σ 2^k/(2^k · k²·(log 2)²) = Σ 1/(k²·(log 2)²)
    is a constant multiple of the convergent Basel p-series (p = 2). -/
theorem logHarmonicSq_summable : Summable logHarmonicSq := by
  rw [← summable_condensed_iff_of_eventually_nonneg
      (Filter.Eventually.of_forall logHarmonicSq_nonneg)
      (by filter_upwards [Filter.eventually_ge_atTop 2] with k hk
          exact logHarmonicSq_antitone hk (Nat.le_succ k))]
  exact condensed_logHarmonicSq_summable

end HarmonicDivergenceOQ02
