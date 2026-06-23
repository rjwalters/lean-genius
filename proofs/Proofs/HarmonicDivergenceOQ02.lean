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
theorem logHarmonic_antitone :
    ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → logHarmonic n ≤ logHarmonic m := by
  intro m n hm hmn
  by_cases hm2 : m < 2
  · -- m = 1: logHarmonic m = 0, logHarmonic n ≥ 0
    have : m = 1 := by omega
    subst this
    simp [logHarmonic]
    split_ifs with h
    · exact le_refl _
    · exact div_nonneg (le_of_lt one_pos) (le_of_lt (mul_log_pos (by omega)))
  · -- m ≥ 2, n ≥ 2: compare 1/(n·log n) ≤ 1/(m·log m)
    push_neg at hm2
    rw [logHarmonic_of_ge_two hm2, logHarmonic_of_ge_two (le_trans hm2 hmn)]
    rw [div_le_div_iff (mul_log_pos (le_trans hm2 hmn)) (mul_log_pos hm2)]
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
  have h_log_pow : Real.log (↑(2 ^ k) : ℝ) = k * Real.log 2 := by
    rw [Nat.cast_pow]
    exact Real.log_pow k 2
  rw [h_log_pow]
  have hk_pos : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hlog2_pos : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have h2k_pos : (↑(2 ^ k) : ℝ) ≠ 0 := by exact_mod_cast (show 2 ^ k ≠ 0 by positivity)
  field_simp
  ring

/-- The condensed logHarmonic series is not summable.
    It equals 1/(k·log 2) for k ≥ 1, which is a rescaled harmonic series. -/
theorem condensed_logHarmonic_not_summable :
    ¬Summable (fun k : ℕ => (2 : ℝ) ^ k * logHarmonic (2 ^ k)) := by
  -- The condensed series for k ≥ 1 is 1/(k·log 2) = (1/log 2)·(1/k)
  -- Since Σ 1/k diverges, so does (1/log 2)·Σ 1/k
  rw [show (fun k : ℕ => (2 : ℝ) ^ k * logHarmonic (2 ^ k)) =
      (fun k => if k = 0 then (2 : ℝ) ^ 0 * logHarmonic (2 ^ 0)
                else 1 / ((k : ℝ) * Real.log 2)) from by
    ext k; by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, condensed_logHarmonic_eq k (by omega)]
  ]
  intro ⟨a, ha⟩
  -- If the full series is summable, then the tail (k ≥ 1) is summable
  have h_tail : Summable (fun k : ℕ => 1 / ((k + 1 : ℝ) * Real.log 2)) := by
    have := ha.comp_injective (fun k => k + 1) (fun a b h => by omega)
    simp only [Function.comp] at this
    convert this using 1
    ext k; simp [show k + 1 ≠ 0 by omega]
  -- This means Σ 1/((k+1)·log 2) converges, so (1/log 2)·Σ 1/(k+1) converges
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h_harmonic : Summable (fun k : ℕ => 1 / (↑(k + 1) : ℝ)) := by
    have := h_tail.mul_left (Real.log 2)
    simp only [mul_comm (Real.log 2), mul_div_assoc'] at this
    convert this using 1
    ext k; rw [div_mul_eq_mul_div, mul_comm, mul_div_mul_left _ _ (ne_of_gt hlog2_pos)]
  -- But Σ 1/(k+1) = Σ_{n≥1} 1/n, which diverges
  exact Real.not_summable_one_div_natCast (Summable.comp_injective h_harmonic
    (fun k => k + 1) (fun a b h => by omega) |>.congr (by intro n; push_cast; ring_nf))

/-- **The log-harmonic series Σ 1/(n·log n) diverges.**

    Proved via the Cauchy condensation test:
    the condensed series Σ 2^k/(2^k · k·log 2) = Σ 1/(k·log 2)
    is a rescaled harmonic series, which diverges. -/
theorem logHarmonic_not_summable : ¬Summable logHarmonic := by
  rw [summable_condensed_iff_of_nonneg logHarmonic_nonneg logHarmonic_antitone]
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

/-- logHarmonicSq is antitone for positive n:
    0 < m ≤ n → logHarmonicSq n ≤ logHarmonicSq m. -/
theorem logHarmonicSq_antitone :
    ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → logHarmonicSq n ≤ logHarmonicSq m := by
  intro m n hm hmn
  by_cases hm2 : m < 2
  · -- m = 1: logHarmonicSq 1 = 0, logHarmonicSq n ≥ 0
    have : m = 1 := by omega
    subst this
    simp [logHarmonicSq]
    split_ifs with h
    · exact le_refl _
    · exact div_nonneg (le_of_lt one_pos) (le_of_lt (mul_log_sq_pos (by omega)))
  · -- m, n ≥ 2: compare 1/(n·(log n)²) ≤ 1/(m·(log m)²)
    push_neg at hm2
    rw [logHarmonicSq_of_ge_two hm2, logHarmonicSq_of_ge_two (le_trans hm2 hmn)]
    rw [div_le_div_iff (mul_log_sq_pos (le_trans hm2 hmn)) (mul_log_sq_pos hm2)]
    simp only [one_mul]
    -- Need: m · (log m)² ≤ n · (log n)²
    have hlog_le : Real.log m ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast (show 0 < m by omega))
        (by exact_mod_cast hmn)
    have hlog_m_nonneg : 0 ≤ Real.log m :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
    apply mul_le_mul
    · exact_mod_cast hmn
    · exact pow_le_pow_left hlog_m_nonneg hlog_le 2
    · exact sq_nonneg _
    · exact Nat.cast_nonneg _

/-- The condensed logHarmonicSq at k ≥ 1 equals 1 / (k² · (log 2)²). -/
theorem condensed_logHarmonicSq_eq (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ k * logHarmonicSq (2 ^ k) = 1 / ((k : ℝ) ^ 2 * (Real.log 2) ^ 2) := by
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  rw [logHarmonicSq_of_ge_two h2k]
  have h_log_pow : Real.log (↑(2 ^ k) : ℝ) = k * Real.log 2 := by
    rw [Nat.cast_pow]
    exact Real.log_pow k 2
  rw [h_log_pow]
  have hk_pos : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hlog2_pos : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have h2k_pos : (↑(2 ^ k) : ℝ) ≠ 0 := by exact_mod_cast (show 2 ^ k ≠ 0 by positivity)
  field_simp
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
  ring

/-- **The squared-log series Σ 1/(n·(log n)²) is summable.**

    Proved via the Cauchy condensation test:
    the condensed series Σ 2^k/(2^k · k²·(log 2)²) = Σ 1/(k²·(log 2)²)
    is a constant multiple of the convergent Basel p-series (p = 2). -/
theorem logHarmonicSq_summable : Summable logHarmonicSq := by
  rw [summable_condensed_iff_of_nonneg logHarmonicSq_nonneg logHarmonicSq_antitone]
  exact condensed_logHarmonicSq_summable

end HarmonicDivergenceOQ02
