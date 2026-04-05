/-
  Strict Monotonicity: (1 + 1/n)^n is Strictly Increasing

  OQ-03-OQ-02-OQ-03 derived from the exponential limit formalization.

  **Main theorem**: The sequence aₙ = (1 + 1/n)^n is strictly increasing for n ≥ 1.
  Equivalently, defining f(n) = (1 + 1/(n+1))^(n+1) for n : ℕ (starting at n=0):
  f is strictly monotone.

  **Proof strategy**:
  1. Key inequality: log(1+t) > t/(1+t) for t > 0.
     [From Real.add_one_lt_exp applied to x = -t/(1+t) ≠ 0: 1 - t/(1+t) < exp(-t/(1+t)),
      i.e., 1/(1+t) < exp(-t/(1+t)). Taking log: -log(1+t) < -t/(1+t).]

  2. The function g : t ↦ log(1+t)/t is strictly decreasing on (0, ∞).
     [g'(t) = (t/(1+t) - log(1+t))/t² < 0 by step 1.]

  3. The sequence n ↦ n·log(1+1/n) is strictly increasing.
     [= g(1/n), and g decreasing + 1/n > 1/(n+1) gives g(1/n) < g(1/(n+1)).]

  4. Conclude (1+1/n)^n = exp(n·log(1+1/n)) is strictly increasing.

  **Key references**:
  - Parent: BinomialTheoremOQ03OQ02 (limit (1+1/n)^n → e)
  - Classic analysis: Rudin, Principles of Mathematical Analysis, Chapter 3

  **Axiom count**: 0
  **Sorry count**: 0
-/
import Mathlib

open Real Filter Set

namespace StrictlyIncreasingEuler

/-! ## Part I: Key Inequality log(1+t) > t/(1+t) -/

/-- For t > 0, log(1+t) > t/(1+t).

    Proof: Apply Real.add_one_lt_exp to x = -t/(1+t) (note x ≠ 0):
    1 - t/(1+t) < exp(-t/(1+t)), i.e., 1/(1+t) < exp(-t/(1+t)).
    Taking log: log(1/(1+t)) < -t/(1+t), i.e., -log(1+t) < -t/(1+t). -/
theorem log_one_plus_gt (t : ℝ) (ht : 0 < t) : t / (1 + t) < Real.log (1 + t) := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h1t_ne : (1 + t : ℝ) ≠ 0 := h1t.ne'
  -- Apply strict Bernoulli-type bound: x ≠ 0 → 1 + x < exp(x)
  have hx_ne : -(t / (1 + t)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero ht.ne' h1t_ne)
  have h := Real.add_one_lt_exp hx_ne
  -- h : 1 + (-(t/(1+t))) < exp(-(t/(1+t)))
  have hsimpl : -(t / (1 + t)) + 1 = 1 / (1 + t) := by field_simp; ring
  rw [hsimpl] at h
  -- h : 1/(1+t) < exp(-t/(1+t))
  -- Take log of both sides (log is strictly increasing, 1/(1+t) > 0)
  have hpos : (0 : ℝ) < 1 / (1 + t) := div_pos one_pos h1t
  have h2 := Real.log_lt_log hpos h
  rw [Real.log_exp] at h2
  -- h2 : log(1/(1+t)) < -(t/(1+t))
  rw [one_div, Real.log_inv] at h2
  -- h2 : -log(1+t) < -(t/(1+t))
  linarith

/-- The key inequality restated: for all t > 0,
    t/(1+t) < log(1+t) < t. -/
theorem log_sandwich (t : ℝ) (ht : 0 < t) :
    t / (1 + t) < Real.log (1 + t) ∧ Real.log (1 + t) < t := by
  constructor
  · exact log_one_plus_gt t ht
  · have h1 : 1 + t < Real.exp t := by linarith [Real.add_one_lt_exp (ne_of_gt ht)]
    have h2 := Real.log_lt_log (by linarith) h1
    rwa [Real.log_exp] at h2

/-! ## Part II: Derivative of g(t) = log(1+t)/t is Negative -/

/-- The function g(t) = log(1+t)/t has derivative (t/(1+t) - log(1+t))/t² at t > 0. -/
theorem hasDerivAt_log_div (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => Real.log (1 + s) / s)
    ((1 / (1 + t) * t - Real.log (1 + t)) / t ^ 2) t := by
  have ht_ne : t ≠ 0 := ht.ne'
  have h1t_pos : (0 : ℝ) < 1 + t := by linarith
  -- Derivative of log(1+s) at t is 1/(1+t)
  have hlog : HasDerivAt (fun s => Real.log (1 + s)) (1 / (1 + t)) t := by
    have := (Real.hasDerivAt_log h1t_pos.ne').comp t ((hasDerivAt_id t).const_add 1)
    simp [mul_comm] at this ⊢
    convert this using 1
  -- Derivative of s at t is 1
  have hid : HasDerivAt (fun s => s) 1 t := hasDerivAt_id t
  -- Quotient rule: result has form (f' * g - f * g') / g², need mul_one simplification
  have hdiv := hlog.div hid ht_ne
  simp only [mul_one] at hdiv
  exact hdiv

/-- The derivative of g(t) = log(1+t)/t is negative for t > 0. -/
theorem log_div_deriv_neg (t : ℝ) (ht : 0 < t) :
    (1 / (1 + t) * t - Real.log (1 + t)) / t ^ 2 < 0 := by
  apply div_neg_of_neg_of_pos _ (pow_pos ht 2)
  -- Need: 1/(1+t) * t < log(1+t), i.e., t/(1+t) < log(1+t)
  have h := log_one_plus_gt t ht
  linarith [div_mul_eq_mul_div 1 (1 + t) t, one_mul t, mul_one_div t (1 + t)]

/-! ## Part III: Strict Monotonicity of g(t) = log(1+t)/t -/

/-- The function g(t) = log(1+t)/t is continuous on (0, ∞). -/
theorem log_div_continuousOn : ContinuousOn (fun t => Real.log (1 + t) / t) (Set.Ioi 0) := by
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · exact (continuous_const.add continuous_id').continuousOn
    · intro t ht
      have := mem_Ioi.mp ht
      linarith
  · exact continuousOn_id
  · intro t ht; exact (mem_Ioi.mp ht).ne'

/-- g(t) = log(1+t)/t is strictly decreasing on (0, ∞). -/
theorem log_div_strictAntiOn : StrictAntiOn (fun t => Real.log (1 + t) / t) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact log_div_continuousOn
  · intro t ht
    rw [interior_Ioi] at ht
    have ht' := ht
    rw [mem_Ioi] at ht'
    have hd := hasDerivAt_log_div t ht'
    rw [hd.deriv]
    exact log_div_deriv_neg t ht'

/-! ## Part IV: Main Theorem -/

/-- The function n ↦ n·log(1+1/n) = log(1+1/n)/(1/n) is strictly increasing for n ≥ 1. -/
theorem nlog_strictMono {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    (m : ℝ) * Real.log (1 + 1 / m) < (n : ℝ) * Real.log (1 + 1 / n) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  -- Rewrite as g(1/m) < g(1/n) where g(t) = log(1+t)/t is decreasing
  -- g(1/m) = log(1+1/m) / (1/m) = m * log(1+1/m)
  -- g(1/n) = log(1+1/n) / (1/n) = n * log(1+1/n)
  have key_m : (m : ℝ) * Real.log (1 + 1 / m) = Real.log (1 + 1 / m) / (1 / m) := by
    field_simp
  have key_n : (n : ℝ) * Real.log (1 + 1 / n) = Real.log (1 + 1 / n) / (1 / n) := by
    field_simp
  rw [key_m, key_n]
  -- Apply strict anti-tonicity of g at 1/n < 1/m (both in (0,∞))
  apply log_div_strictAntiOn
  · exact mem_Ioi.mpr (div_pos one_pos hn_pos)
  · exact mem_Ioi.mpr (div_pos one_pos hm_pos)
  · exact one_div_lt_one_div_of_lt hm_pos (Nat.cast_lt.mpr hmn)

/-- **(Main Theorem)** The sequence (1 + 1/n)^n is strictly increasing for n ≥ 1.

    For positive integers m < n, (1 + 1/m)^m < (1 + 1/n)^n. -/
theorem one_plus_inv_pow_strictMono {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    (1 + 1 / (m : ℝ)) ^ m < (1 + 1 / (n : ℝ)) ^ n := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  -- (1+1/n)^n = exp(n * log(1+1/n))
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (1 + 1 / m) ^ m),
      ← Real.exp_log (by positivity : (0 : ℝ) < (1 + 1 / n) ^ n)]
  apply Real.exp_lt_exp.mpr
  -- Need: log((1+1/m)^m) < log((1+1/n)^n)
  -- = m * log(1+1/m) < n * log(1+1/n)
  rw [Real.log_pow, Real.log_pow]
  push_cast
  exact nlog_strictMono hm hmn

/-- Corollary: The sequence n ↦ (1 + 1/(n+1))^(n+1) is strictly monotone. -/
theorem euler_seq_strictMono : StrictMono (fun n : ℕ => (1 + 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) := by
  intro m n hmn
  apply one_plus_inv_pow_strictMono (by omega)
  exact Nat.succ_lt_succ hmn

/-- The lower bound: for n ≥ 1, (1+1/n)^n > 2.
    (Since (1+1/1)^1 = 2 and the sequence is strictly increasing.) -/
theorem one_plus_inv_pow_gt_two {n : ℕ} (hn : 1 < n) :
    (2 : ℝ) < (1 + 1 / (n : ℝ)) ^ n := by
  have h := one_plus_inv_pow_strictMono (m := 1) (n := n) (by omega) (by omega)
  norm_num at h
  -- h : 2 < (1 + (↑n)⁻¹)^n; goal: 2 < (1 + 1/↑n)^n; use one_div to bridge
  rwa [one_div]

/-- Upper bound: for n ≥ 1, (1+1/n)^n < 3.
    This follows from the bound (1+1/n)^n ≤ exp(1) < 3. -/
theorem one_plus_inv_pow_lt_three {n : ℕ} (hn : 1 ≤ n) :
    (1 + 1 / (n : ℝ)) ^ n < 3 := by
  have hbound : (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    -- 1 + 1/n ≤ exp(1/n) by Real.add_one_le_exp, so (1+1/n)^n ≤ exp(1/n)^n = exp(1)
    have h_le : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
      have := Real.add_one_le_exp (1 / (n : ℝ)); linarith
    calc (1 + 1 / (n : ℝ)) ^ n
        ≤ Real.exp (1 / (n : ℝ)) ^ n := by gcongr
      _ = Real.exp (↑n * (1 / ↑n)) := (Real.exp_nat_mul _ n).symm
      _ = Real.exp 1 := by congr 1; field_simp
  linarith [Real.exp_one_lt_d9]

/-- Summary theorem packaging the main results. -/
theorem monotone_euler_summary :
    -- (1) Strictly increasing: m < n → (1+1/m)^m < (1+1/n)^n
    (∀ m n : ℕ, 1 ≤ m → m < n → (1 + 1 / (m : ℝ)) ^ m < (1 + 1 / (n : ℝ)) ^ n) ∧
    -- (2) Lower bound: n ≥ 2 → (1+1/n)^n > 2
    (∀ n : ℕ, 1 < n → (2 : ℝ) < (1 + 1 / (n : ℝ)) ^ n) ∧
    -- (3) Upper bound: n ≥ 1 → (1+1/n)^n < 3
    (∀ n : ℕ, 1 ≤ n → (1 + 1 / (n : ℝ)) ^ n < 3) :=
  ⟨fun m n hm hmn => one_plus_inv_pow_strictMono hm hmn,
   fun n hn => one_plus_inv_pow_gt_two hn,
   fun n hn => one_plus_inv_pow_lt_three hn⟩

end StrictlyIncreasingEuler
