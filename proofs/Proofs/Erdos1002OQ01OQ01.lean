/-
Erdős Problem #1002 — OQ-01-OQ-01: Weyl Equidistribution

Proves Weyl's exponential sum criterion for irrational rotations:
  For irrational α and k ∈ ℤ \ {0}:
    (1/N) · ‖∑_{n=0}^{N-1} e^{2πiknα}‖ → 0

This is the key computational engine of Weyl's equidistribution theorem,
showing the fractional parts {nα} become uniformly distributed mod 1.

**Proved in this file**:
- `irrational_exp_ne_one`: exp(2πikα) ≠ 1 for irrational α, k ≠ 0
- `weyl_cesaro_bound`: geometric series norm bound 2/‖r-1‖ for ‖r‖=1, r≠1
- `weyl_cesaro_zero`: Cesàro mean ‖∑ e^{2πiknα}‖/N → 0 for irrational α

**Stated with sorry** (requires Fourier analysis):
- `weyl_fract_average_zero`: (1/n)·innerSum α n → 0 for irrational α

The log bound requires continued fraction theory and is axiomatized.

Reference: Weyl, H. (1916). Über die Gleichverteilung von Zahlen mod. Eins.
-/

import Mathlib

set_option maxHeartbeats 800000

open Real Filter Finset

namespace Erdos1002OQ01OQ01

/-! ## Setup -/

/-- Deviation from midpoint: 1/2 - {x}. -/
noncomputable def deviation (x : ℝ) : ℝ := 1 / 2 - Int.fract x

/-- Inner sum: S(α, n) = Σ_{k=1}^n (1/2 - {αk}). -/
noncomputable def innerSum (α : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, deviation (α * (↑k + 1))

/-! ## Part I: exp(2πikα) ≠ 1 for irrational α, k ≠ 0 -/

/-- For irrational α and k ∈ ℤ \ {0}, exp(2πikα) ≠ 1.
    Proof: if exp(2πikα) = 1, then 2πikα = n·2πi for some n : ℤ,
    so kα = n, making α = n/k ∈ ℚ — contradiction. -/
theorem irrational_exp_ne_one (α : ℝ) (hα : Irrational α) (k : ℤ) (hk : k ≠ 0) :
    Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  -- Cancel 2πI to get kα = n
  have h2πI : (2 : ℂ) * ↑π * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have heq : (k : ℂ) * α = n :=
    mul_left_cancel₀ h2πI (by linear_combination hn)
  have heq_real : (k : ℝ) * α = n := by exact_mod_cast heq
  -- α = n/k is rational — contradicts irrational α
  have hk_ne : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  apply hα
  exact ⟨(n : ℚ) / k, by
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
    field_simp [hk_ne]
    linarith⟩

/-! ## Part II: Geometric Series Bound -/

/-- exp(2πikα) has norm 1 (it lies on the unit circle). -/
private theorem exp_norm_one (α : ℝ) (k : ℤ) :
    ‖Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α)‖ = 1 := by
  have h : 2 * ↑π * Complex.I * ↑k * ↑α = ↑(2 * π * ↑k * α) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- For r with ‖r‖ = 1 and r ≠ 1, the partial geometric sum satisfies
    ‖∑_{k=0}^{N-1} r^k‖ ≤ 2 / ‖r - 1‖.
    Proof: sum = (r^N-1)/(r-1); |r^N-1| ≤ |r^N|+1 = 2. -/
theorem weyl_cesaro_bound (r : ℂ) (hr : ‖r‖ = 1) (h1 : r ≠ 1) (N : ℕ) :
    ‖∑ k ∈ range N, r ^ k‖ ≤ 2 / ‖r - 1‖ := by
  have hdenom_pos : 0 < ‖r - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp; positivity
  · -- bound |r^N - 1| ≤ 2
    have hr_pow : ‖r ^ N‖ = 1 := by rw [norm_pow, hr, one_pow]
    have h_num_bound : ‖r ^ N - 1‖ ≤ 2 :=
      calc ‖r ^ N - 1‖ ≤ ‖r ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + 1 := by rw [hr_pow, norm_one]
        _ = 2 := by norm_num
    rw [geom_sum_eq h1, norm_div]
    exact div_le_div_of_nonneg_right h_num_bound hdenom_pos.le

/-! ## Part III: Cesàro Mean Tends to Zero -/

/-- **Weyl's criterion (Cesàro form)**: For irrational α and k ∈ ℤ \ {0},
    ‖∑_{n=0}^{N-1} e^{2πiknα}‖ / N → 0.

    The sum is bounded by 2/‖exp(2πikα) - 1‖ (independent of N),
    so dividing by N → ∞ gives convergence to 0. -/
theorem weyl_cesaro_zero (α : ℝ) (hα : Irrational α) (k : ℤ) (hk : k ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => ‖∑ n ∈ range N,
        Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n)‖ / N)
      Filter.atTop (nhds 0) := by
  -- r = exp(2πikα): on the unit circle, ≠ 1
  set r := Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α) with hr_def
  have hr_norm : ‖r‖ = 1 := exp_norm_one α k
  have hr_ne : r ≠ 1 := irrational_exp_ne_one α hα k hk
  -- Each summand equals a power of r
  have hterm : ∀ n : ℕ, Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n) = r ^ n := fun n => by
    simp only [hr_def]; rw [← Complex.exp_nat_mul]; congr 1; ring
  -- Squeeze: 0 ≤ ‖∑ r^n‖/N ≤ (2/‖r-1‖)/N → 0
  have h_bound : ∀ N : ℕ,
      ‖∑ n ∈ range N, Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n)‖ / N ≤
      (2 / ‖r - 1‖) / N := fun N => by
    simp_rw [hterm]
    exact div_le_div_of_nonneg_right (weyl_cesaro_bound r hr_norm hr_ne N) (Nat.cast_nonneg _)
  exact squeeze_zero
    (fun N => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    h_bound
    (tendsto_const_div_atTop_nhds_zero_nat (2 / ‖r - 1‖))

/-! ## Part IV: Equidistribution for Continuous Functions

The key intermediate result: for continuous periodic g,
  (1/N) ∑_{n<N} g(nα) → ∫₀¹ g(x) dx

Proof via density of trigonometric polynomials:
1. For trig poly P(x) = Σ cₖ e^{2πikx}: (1/N)ΣP(nα) → c₀ = ∫P by weyl_cesaro_zero
2. By `span_fourier_closure_eq_top` (Mathlib), trig polys are dense in C(ℝ/ℤ)
3. For continuous g, find P with ‖g-P‖_∞ < ε; then |(1/N)Σg - (1/N)ΣP| ≤ ε
4. Since (1/N)ΣP → ∫P and |∫P - ∫g| ≤ ε, we get |(1/N)Σg - ∫g| ≤ 2ε
-/

/-- **Weyl's equidistribution for continuous periodic functions**.
    For irrational α and continuous g with period 1,
    (1/N) Σ g(α*(n+1)) → ∫₀¹ g.

    This is the key missing lemma. Proof requires connecting `weyl_cesaro_zero`
    to the density of trigonometric polynomials
    (`span_fourier_closure_eq_top` on `AddCircle 1`). -/
theorem weyl_equidist_continuous (α : ℝ) (hα : Irrational α)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (hg_per : ∀ x, g (x + 1) = g x) :
    Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ range N, g (α * (↑n + 1))) / ↑N)
      Filter.atTop (nhds (∫ x in (0 : ℝ)..1, g x)) := by
  sorry

/-! ## Part IV-B: Fractional Part Average

Given `weyl_equidist_continuous`, the result for the discontinuous
function deviation(x) = 1/2 - {x} follows by a sandwich argument:
- Construct continuous periodic g⁻ ≤ deviation ≤ g⁺ with |∫g±| ≤ ε
- Apply `weyl_equidist_continuous` to g± to get (1/N)Σg± → ∫g± ≈ 0
- Pointwise bounds give (1/N)Σg⁻ ≤ innerSum/N ≤ (1/N)Σg⁺
- Squeeze: innerSum/N → 0
-/

/-- For irrational α, (1/n) · S(α,n) → 0.
    Proof requires `weyl_equidist_continuous` + continuous sandwich of deviation. -/
theorem weyl_fract_average_zero (α : ℝ) (hα : Irrational α) :
    Filter.Tendsto (fun n : ℕ => innerSum α n / n) Filter.atTop (nhds 0) := by
  sorry

/-! ## Part V: Inner Sum Log Bound (axiomatized)

The log bound |S(α,n)| ≤ C·log n holds for "badly approximable" irrationals
(bounded continued fraction coefficients). This requires diophantine approximation.

Badly approximable examples: √2, φ = (1+√5)/2 (all bounded partial quotients).
Liouville numbers (arbitrarily good rational approximations) may grow faster. -/

/-- Distance from x to nearest integer: min({x}, 1-{x}). -/
noncomputable def distToNearestInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- α has bounded partial quotients: ‖qα‖ ≥ C/q for all q ≥ 1.
    Equivalently: the continued fraction coefficients are uniformly bounded. -/
def HasBoundedPartialQuotients (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → distToNearestInt (q * α) ≥ C / q

/-- **Inner sum log bound** (axiom: requires continued fraction theory).
    For badly approximable irrational α, |S(α,n)| ≤ C·log n. -/
axiom innerSum_log_bound (α : ℝ) (hα : Irrational α) (hbpq : HasBoundedPartialQuotients α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → |innerSum α n| ≤ C * Real.log n

/-- The log-normalized function is bounded for badly approximable α. -/
theorem log_normalized_bounded (α : ℝ) (hα : Irrational α) (hbpq : HasBoundedPartialQuotients α) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |innerSum α n / Real.log n| ≤ C := by
  obtain ⟨C, _, hC⟩ := innerSum_log_bound α hα hbpq
  refine ⟨C, fun n hn => ?_⟩
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast show 1 < n from by omega)
  rw [abs_div, abs_of_pos hlog_pos]
  -- |innerSum α n| / log n ≤ C from |innerSum α n| ≤ C * log n
  have h_le : |innerSum α n| / Real.log n ≤ C * Real.log n / Real.log n :=
    div_le_div_of_nonneg_right (hC n hn) hlog_pos.le
  have h_simp : C * Real.log n / Real.log n = C := mul_div_cancel_right₀ C hlog_pos.ne'
  linarith

end Erdos1002OQ01OQ01
