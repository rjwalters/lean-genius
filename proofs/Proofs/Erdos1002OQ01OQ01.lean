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
- `weyl_equidist_continuous`: equidistribution for continuous periodic functions
    (proved modulo `equidist_approx` — density of trig polynomials)
- `weyl_fract_average_zero`: (1/n)·innerSum α n → 0 for irrational α
    (proved modulo `deviation_sandwich` — continuous approximation of deviation)

**Remaining sorry** (well-scoped, independently provable):
- `equidist_approx`: density of trig polys via `span_fourier_closure_eq_top`

`deviation_sandwich` is now fully proved.

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

/-! ## Part III-B: Real-Part and Imaginary-Part Corollaries

These corollaries extract real/imaginary parts from weyl_cesaro_zero.
They are used in approximation arguments (e.g. bounding trig poly Cesàro averages). -/

/-- **Weyl's criterion for real parts**: For irrational α and k ∈ ℤ \ {0},
    (1/N) Σ_{n<N} Re(e^{2πiknα}) → 0.

    Proof: Re(∑ exp)/N = (∑ Re(exp))/N. Apply Re-continuity to weyl_cesaro_zero. -/
theorem weyl_cesaro_re_zero (α : ℝ) (hα : Irrational α) (k : ℤ) (hk : k ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ range N,
        (Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n)).re) / N)
      Filter.atTop (nhds 0) := by
  have h := weyl_cesaro_zero α hα k hk
  -- Bound |(∑ Re(exp))/N| ≤ ‖(∑ exp)/N‖ and the latter → 0 by weyl_cesaro_zero
  apply squeeze_zero_norm
      (g := fun N => ‖(∑ n ∈ range N, Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n)) /
        (N : ℂ)‖)
  · intro N
    rw [Real.norm_eq_abs, abs_div, abs_natCast, norm_div, Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hsum_re : |(∑ n ∈ range N, (Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n)).re)| =
        |(∑ n ∈ range N, Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n)).re| := by
      congr 1; exact (map_sum Complex.reAddGroupHom _ _).symm
    rw [hsum_re]; exact Complex.norm_re_le_norm _
  · simpa using h.norm

/-- **Weyl's criterion for imaginary parts**: For irrational α and k ∈ ℤ \ {0},
    (1/N) Σ_{n<N} Im(e^{2πiknα}) → 0. -/
theorem weyl_cesaro_im_zero (α : ℝ) (hα : Irrational α) (k : ℤ) (hk : k ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ range N,
        (Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n)).im) / N)
      Filter.atTop (nhds 0) := by
  have h := weyl_cesaro_zero α hα k hk
  apply squeeze_zero_norm
      (g := fun N => ‖(∑ n ∈ range N, Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n)) /
        (N : ℂ)‖)
  · intro N
    rw [Real.norm_eq_abs, abs_div, abs_natCast, norm_div, Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hsum_im : |(∑ n ∈ range N, (Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n)).im)| =
        |(∑ n ∈ range N, Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n)).im| := by
      congr 1; exact (map_sum Complex.imAddGroupHom _ _).symm
    rw [hsum_im]; exact Complex.norm_im_le_norm _
  · simpa using h.norm

/-! ## Part IV: Equidistribution for Continuous Functions

Strategy (ε-approximation via density of trigonometric polynomials):
1. By `span_fourier_closure_eq_top` (Stone-Weierstrass on `AddCircle 1`),
   approximate g uniformly by a trig polynomial P with ‖g - P‖_∞ < ε/3
2. For trig polynomial P, (1/N)ΣP(nα) → ∫P by `weyl_cesaro_zero` + linearity
3. Triangle: |avg(g) - ∫g| ≤ |avg(g) - avg(P)| + |avg(P) - ∫P| + |∫P - ∫g| < ε
-/

/-- Approximation lemma: continuous periodic functions can be uniformly
    approximated by functions whose irrational rotation averages converge.
    The approximant is a trigonometric polynomial; existence follows from
    `span_fourier_closure_eq_top` on `AddCircle 1`, convergence of its
    averages from `weyl_cesaro_zero` applied to each Fourier mode. -/
private lemma equidist_approx (α : ℝ) (hα : Irrational α)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (hg_per : ∀ x, g (x + 1) = g x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (h : ℝ → ℝ),
      (∀ x, |g x - h x| ≤ ε) ∧
      (|∫ x in (0 : ℝ)..1, g x - ∫ x in (0 : ℝ)..1, h x| ≤ ε) ∧
      Filter.Tendsto
        (fun N : ℕ => (∑ n ∈ range N, h (α * (↑n + 1))) / ↑N)
        Filter.atTop (nhds (∫ x in (0 : ℝ)..1, h x)) := by
  -- Combined density + integral sorry: Stone-Weierstrass gives Fourier polynomial
  -- h = Σ_{k∈cs} Re(Aₖ e^{2πikx}) within ε of g, with integral = Σ_{k=0} Re(A₀).
  -- Uses span_fourier_closure_eq_top (AddCircle.liftIco) + trig period integrals.
  obtain ⟨cs, A, hclose, hintA⟩ :
      ∃ (cs : Finset ℤ) (A : ℤ → ℂ),
        (∀ x : ℝ, |g x - ∑ k ∈ cs, (A k * Complex.exp (2 * ↑π * Complex.I * ↑k * ↑x)).re| ≤ ε) ∧
        (∫ x in (0:ℝ)..1, ∑ k ∈ cs, (A k * Complex.exp (2 * ↑π * Complex.I * ↑k * ↑x)).re =
          ∑ k ∈ cs, if k = 0 then (A k).re else 0) := by
    sorry  -- Stone-Weierstrass (span_fourier_closure_eq_top) + trig period integrals
  let h : ℝ → ℝ := fun x => ∑ k ∈ cs, (A k * Complex.exp (2 * ↑π * Complex.I * ↑k * ↑x)).re
  have hh_cont : Continuous h := continuous_finset_sum cs fun k _ =>
    Complex.continuous_re.comp ((continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (continuous_const.mul continuous_id')))).comp continuous_id')
  refine ⟨h, hclose, ?_, ?_⟩
  -- (B): |∫g - ∫h| ≤ ε from pointwise bound
  · rw [← intervalIntegral.integral_sub (hg_cont.intervalIntegrable 0 1)
          (hh_cont.intervalIntegrable 0 1)]
    calc |∫ x in (0:ℝ)..1, (g x - h x)|
        ≤ ∫ x in (0:ℝ)..1, |g x - h x| :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ _x in (0:ℝ)..1, ε := intervalIntegral.integral_mono_on (by norm_num)
          ((hg_cont.sub hh_cont).abs.intervalIntegrable 0 1) intervalIntegrable_const
          (fun x _ => hclose x)
      _ = ε := by simp [intervalIntegral.integral_const]
  -- (C): CONVERGENCE — Cesàro average of h → ∫₀¹ h.
  -- ∫₀¹ h = Σ_{k∈cs} (if k=0 then Re(A₀) else 0)  [given by hintA]
  -- Each mode converges: k=0 → Re(A₀), k≠0 → 0 [Weyl criterion].
  show Filter.Tendsto (fun N => (∑ n ∈ range N, h (α * (↑n + 1))) / ↑N) atTop
      (nhds (∫ x in (0:ℝ)..1, h x))
  rw [hintA]
  -- Exchange Σ_n and Σ_k
  simp_rw [show ∀ N : ℕ, (∑ n ∈ range N, h (α * (↑n + 1))) / ↑N =
      ∑ k ∈ cs, (∑ n ∈ range N,
        (A k * Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * (↑n + 1))).re) / ↑N
      from fun N => by
        simp only [h]; push_cast
        rw [← Finset.sum_div, Finset.sum_comm]
        congr 1; ext n; apply Finset.sum_congr rfl; intro k _; push_cast; ring_nf]
  apply tendsto_finset_sum; intro k _
  by_cases hk : k = 0
  · -- k = 0: constant Re(A₀) for N ≥ 1
    subst hk; simp only [ite_true, Int.cast_zero, zero_mul, Complex.exp_zero, mul_one, mul_zero]
    apply Filter.Tendsto.congr' tendsto_const_nhds
    apply Filter.eventually_atTop.mpr ⟨1, fun N hN => ?_⟩
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hN))]
  · -- k ≠ 0: → 0 by Weyl criterion
    simp only [if_neg hk]
    -- Aₖ e^{2πikα(n+1)} = Cₖ · e^{2πikαn} where Cₖ = Aₖ e^{2πikα}
    set Ck : ℂ := A k * Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α)
    have hfactor : ∀ n : ℕ,
        A k * Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * (↑n + 1)) =
        Ck * Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n) := fun n => by
      simp [Ck, ← Complex.exp_add]; push_cast; ring_nf; congr 1; ring
    simp_rw [fun n => show (A k * Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * (↑n + 1))).re =
        Ck.re * (Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n)).re -
        Ck.im * (Complex.exp (2 * ↑π * Complex.I * ↑k * ↑α * ↑n)).im
        from by rw [hfactor n]; exact Complex.mul_re Ck _,
      Finset.sum_sub_distrib, ← Finset.mul_sum, mul_div_assoc]
    rw [show (0 : ℝ) = Ck.re * 0 - Ck.im * 0 from by ring]
    exact ((weyl_cesaro_re_zero α hα k hk).const_mul Ck.re).sub
          ((weyl_cesaro_im_zero α hα k hk).const_mul Ck.im)

/-- **Weyl's equidistribution for continuous periodic functions**.
    For irrational α and continuous g with period 1,
    (1/N) Σ g(α*(n+1)) → ∫₀¹ g.

    Proof: approximate g by h via `equidist_approx`, then triangle inequality
    |avg(g) - ∫g| ≤ |avg(g) - avg(h)| + |avg(h) - ∫h| + |∫h - ∫g|. -/
theorem weyl_equidist_continuous (α : ℝ) (hα : Irrational α)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (hg_per : ∀ x, g (x + 1) = g x) :
    Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ range N, g (α * (↑n + 1))) / ↑N)
      Filter.atTop (nhds (∫ x in (0 : ℝ)..1, g x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨h, h_close, h_int_close, h_conv⟩ :=
    equidist_approx α hα g hg_cont hg_per (ε / 3) (by linarith)
  rw [Metric.tendsto_atTop] at h_conv
  obtain ⟨N₀, hN₀⟩ := h_conv (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  -- Bound 1: |avg(g) - avg(h)| ≤ ε/3
  have hbd1 : dist ((∑ n ∈ range N, g (α * (↑n + 1))) / ↑N)
      ((∑ n ∈ range N, h (α * (↑n + 1))) / ↑N) ≤ ε / 3 := by
    simp only [Real.dist_eq]
    by_cases hN0 : N = 0
    · simp [hN0]; linarith
    · have hNpos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
      rw [div_sub_div_eq_sub_div, abs_div, abs_of_nonneg hNpos.le, div_le_div_right hNpos,
        show ∑ n ∈ range N, g (α * (↑n + 1)) - ∑ n ∈ range N, h (α * (↑n + 1)) =
          ∑ n ∈ range N, (g (α * (↑n + 1)) - h (α * (↑n + 1))) from
          (Finset.sum_sub_distrib).symm]
      calc |∑ n ∈ range N, (g (α * (↑n + 1)) - h (α * (↑n + 1)))|
          ≤ ∑ n ∈ range N, |g (α * (↑n + 1)) - h (α * (↑n + 1))| := by
            rw [← Real.norm_eq_abs]; simp_rw [← Real.norm_eq_abs]; exact norm_sum_le _ _
        _ ≤ ∑ _n ∈ range N, (ε / 3) :=
            Finset.sum_le_sum (fun n _ => h_close _)
        _ = ε / 3 * ↑N := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Bound 2: |avg(h) - ∫h| < ε/3
  have hbd2 : dist ((∑ n ∈ range N, h (α * (↑n + 1))) / ↑N)
      (∫ x in (0 : ℝ)..1, h x) < ε / 3 := hN₀ N hN
  -- Bound 3: |∫h - ∫g| ≤ ε/3
  have hbd3 : dist (∫ x in (0 : ℝ)..1, h x) (∫ x in (0 : ℝ)..1, g x) ≤ ε / 3 := by
    rw [Real.dist_eq, abs_sub_comm]; exact h_int_close
  -- Combine via triangle inequality
  calc dist ((∑ n ∈ range N, g (α * (↑n + 1))) / ↑N) (∫ x in (0 : ℝ)..1, g x)
      ≤ dist ((∑ n ∈ range N, g (α * (↑n + 1))) / ↑N)
          ((∑ n ∈ range N, h (α * (↑n + 1))) / ↑N) +
        dist ((∑ n ∈ range N, h (α * (↑n + 1))) / ↑N) (∫ x in (0 : ℝ)..1, g x) :=
        dist_triangle _ _ _
    _ ≤ dist ((∑ n ∈ range N, g (α * (↑n + 1))) / ↑N)
          ((∑ n ∈ range N, h (α * (↑n + 1))) / ↑N) +
        (dist ((∑ n ∈ range N, h (α * (↑n + 1))) / ↑N) (∫ x in (0 : ℝ)..1, h x) +
         dist (∫ x in (0 : ℝ)..1, h x) (∫ x in (0 : ℝ)..1, g x)) := by
        linarith [dist_triangle ((∑ n ∈ range N, h (α * (↑n + 1))) / ↑N)
          (∫ x in (0 : ℝ)..1, h x) (∫ x in (0 : ℝ)..1, g x)]
    _ < ε / 3 + (ε / 3 + ε / 3) := by linarith
    _ = ε := by ring

/-! ## Part IV-B: Fractional Part Average

Given `weyl_equidist_continuous`, the result for the discontinuous
function deviation(x) = 1/2 - {x} follows by a sandwich argument:
- Construct continuous periodic g⁻ ≤ deviation ≤ g⁺ with ∫g⁺ ≤ ε, ∫g⁻ ≥ -ε
- Apply `weyl_equidist_continuous` to g± to get (1/N)Σg± → ∫g± ≈ 0
- Pointwise bounds: (1/N)Σg⁻ ≤ innerSum/N ≤ (1/N)Σg⁺
- Squeeze: innerSum/N → 0
-/

/-! ### Sandwich construction helpers

The sandwich functions smooth out the jump discontinuity of `deviation` at integers.
- `sandwichUpCore δ t = 1/2 - t + max(0, t-(1-δ))/δ`: on [1-δ, 1], interpolates
  linearly from -1/2+δ to 1/2 (instead of jumping). Core(0) = Core(1) = 1/2.
- `sandwichLoCore δ t = 1/2 - t - max(0, δ-t)/δ`: on [0, δ], interpolates
  linearly from -1/2 to 1/2-δ (instead of jumping). Core(0) = Core(1) = -1/2.

Composing with `Int.fract` yields continuous periodic functions because the
endpoint condition (f(0) = f(1)) ensures the periodic extension is seamless. -/

/-- Upper sandwich core: smoothly closes the upward jump of deviation at integers. -/
private noncomputable def sandwichUpCore (δ : ℝ) (t : ℝ) : ℝ :=
  1/2 - t + max 0 (t - (1 - δ)) / δ

/-- Lower sandwich core: smoothly closes the downward approach at integers. -/
private noncomputable def sandwichLoCore (δ : ℝ) (t : ℝ) : ℝ :=
  1/2 - t - max 0 (δ - t) / δ

private lemma sandwichUpCore_continuous (δ : ℝ) (hδ : 0 < δ) :
    Continuous (sandwichUpCore δ) := by
  unfold sandwichUpCore
  exact ((continuous_const.sub continuous_id).add
    ((continuous_const.max (continuous_id.sub continuous_const)).div
      continuous_const (fun _ => hδ.ne')))

private lemma sandwichLoCore_continuous (δ : ℝ) (hδ : 0 < δ) :
    Continuous (sandwichLoCore δ) := by
  unfold sandwichLoCore
  exact ((continuous_const.sub continuous_id).sub
    ((continuous_const.max (continuous_const.sub continuous_id)).div
      continuous_const (fun _ => hδ.ne')))

private lemma sandwichUpCore_endpoints (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    sandwichUpCore δ 0 = sandwichUpCore δ 1 := by
  simp only [sandwichUpCore]
  have h0 : max (0 : ℝ) (0 - (1 - δ)) = 0 := max_eq_left (by linarith)
  have h1 : max (0 : ℝ) (1 - (1 - δ)) = δ := by
    rw [show (1 : ℝ) - (1 - δ) = δ from by ring]; exact max_eq_right hδ.le
  rw [h0, h1]; field_simp

private lemma sandwichLoCore_endpoints (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    sandwichLoCore δ 0 = sandwichLoCore δ 1 := by
  simp only [sandwichLoCore]
  have h0 : max (0 : ℝ) (δ - 0) = δ := by rw [sub_zero]; exact max_eq_right hδ.le
  have h1 : max (0 : ℝ) (δ - 1) = 0 := max_eq_left (by linarith)
  rw [h0, h1]; field_simp

/-- A continuous function composed with `Int.fract` is continuous, provided f(0) = f(1).
    At non-integers, `Int.fract` is locally `x - ⌊x⌋` (continuous). At integers,
    the endpoint condition ensures left limit f(1) = f(0) = right limit. -/
private lemma continuous_comp_fract {f : ℝ → ℝ} (hf : Continuous f) (h01 : f 0 = f 1) :
    Continuous (fun x => f (Int.fract x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hfx : Int.fract x = 0
  · -- x is an integer: f(fract(x)) = f(0)
    -- fract is discontinuous at integers, but f(0) = f(1) bridges the gap:
    -- right of x: fract(y) → 0⁺, so f(fract(y)) → f(0)
    -- left of x:  fract(y) → 1⁻, so f(fract(y)) → f(1) = f(0)
    have hxfl : x = ↑⌊x⌋ := by
      have : Int.fract x = x - ↑⌊x⌋ := rfl; linarith
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hf0 : ContinuousAt f 0 := hf.continuousAt
    have hf1 : ContinuousAt f 1 := hf.continuousAt
    obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.mp hf0 ε hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousAt_iff.mp hf1 ε hε
    refine ⟨min (min δ₁ δ₂) 1, lt_min (lt_min hδ₁ hδ₂) one_pos, fun y hy => ?_⟩
    simp only [hfx]
    rw [Real.dist_eq] at hy
    have hyd₁ : |y - x| < δ₁ :=
      lt_of_lt_of_le hy (le_trans (min_le_left _ _) (min_le_left _ _))
    have hyd₂ : |y - x| < δ₂ :=
      lt_of_lt_of_le hy (le_trans (min_le_left _ _) (min_le_right _ _))
    have hy1 : |y - x| < 1 := lt_of_lt_of_le hy (min_le_right _ _)
    have hyl : x - 1 < y := by linarith [(abs_lt.mp hy1).1]
    have hyr : y < x + 1 := by linarith [(abs_lt.mp hy1).2]
    by_cases hge : x ≤ y
    · -- Right case: y ∈ [x, x+1), ⌊y⌋ = ⌊x⌋, fract(y) = y - x ≈ 0
      have hfl : ⌊y⌋ = ⌊x⌋ := by
        apply le_antisymm
        · have : (↑⌊y⌋ : ℝ) < ↑⌊x⌋ + 1 := (Int.floor_le y).trans_lt (by linarith)
          have : ⌊y⌋ < ⌊x⌋ + 1 := by exact_mod_cast this
          omega
        · exact Int.le_floor.mpr (show (↑⌊x⌋ : ℝ) ≤ y by linarith)
      have hfr : Int.fract y = y - x := by
        unfold Int.fract; rw [show (⌊y⌋ : ℝ) = (⌊x⌋ : ℝ) from by exact_mod_cast hfl]; linarith
      rw [hfr]; apply h₁; rwa [Real.dist_eq, sub_zero]
    · -- Left case: y ∈ (x-1, x), ⌊y⌋ = ⌊x⌋ - 1, fract(y) = y - x + 1 ≈ 1
      push_neg at hge
      have hfl : ⌊y⌋ = ⌊x⌋ - 1 := by
        apply le_antisymm
        · have : (↑⌊y⌋ : ℝ) < ↑⌊x⌋ := (Int.floor_le y).trans_lt (by linarith)
          have : ⌊y⌋ < ⌊x⌋ := by exact_mod_cast this
          omega
        · exact Int.le_floor.mpr (show (↑(⌊x⌋ - 1) : ℝ) ≤ y by push_cast; linarith)
      have hfr : Int.fract y = y - x + 1 := by
        unfold Int.fract; rw [show (⌊y⌋ : ℝ) = (⌊x⌋ : ℝ) - 1 from by push_cast; exact_mod_cast hfl]
        linarith
      rw [hfr, h01]; apply h₂
      rw [Real.dist_eq, show y - x + 1 - 1 = y - x from by ring]
      exact hyd₂
  · -- x is not an integer: fract is locally y ↦ y - ⌊x⌋, which is continuous
    have hfr_pos : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hfx)
    -- f ∘ fract agrees with f ∘ (· - ⌊x⌋) in a neighborhood of x
    have h_eq : (fun y => f (Int.fract y)) =ᶠ[nhds x] (fun y => f (y - ↑⌊x⌋)) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Set.Ioo ↑⌊x⌋ (↑⌊x⌋ + 1),
        IsOpen.mem_nhds isOpen_Ioo ⟨?_, Int.lt_floor_add_one x⟩, fun y hy => ?_⟩
      · -- ⌊x⌋ < x because fract(x) > 0
        have : Int.fract x = x - ↑⌊x⌋ := rfl
        linarith
      · -- On (⌊x⌋, ⌊x⌋+1), ⌊y⌋ = ⌊x⌋ so fract(y) = y - ⌊x⌋
        congr 1
        have hfloor_eq : ⌊y⌋ = ⌊x⌋ := by
          apply le_antisymm
          · -- ⌊y⌋ ≤ ⌊x⌋ from ⌊y⌋ ≤ y < ⌊x⌋+1
            rw [← Int.lt_add_one_iff]
            exact_mod_cast (Int.floor_le y).trans_lt hy.2
          · -- ⌊x⌋ ≤ ⌊y⌋ from ⌊x⌋ ≤ y
            exact Int.le_floor.mpr hy.1.le
        simp [Int.fract, hfloor_eq]
    exact h_eq.symm.continuousAt ((hf.comp (continuous_id.sub continuous_const)).continuousAt)

/-- Continuous sandwich of the deviation function: for ε > 0, there exist
    continuous periodic g_lo ≤ deviation ≤ g_up with integrals near zero.

    Construction: `sandwichUpCore δ ∘ fract` and `sandwichLoCore δ ∘ fract` where
    `δ = min(ε, 1/2)`. The core functions smooth the jump at integers by replacing
    the discontinuous region with a linear interpolant. -/
private lemma deviation_sandwich (ε : ℝ) (hε : 0 < ε) :
    ∃ (g_lo g_up : ℝ → ℝ),
      Continuous g_lo ∧ Continuous g_up ∧
      (∀ x, g_lo (x + 1) = g_lo x) ∧ (∀ x, g_up (x + 1) = g_up x) ∧
      (∀ x, g_lo x ≤ deviation x) ∧ (∀ x, deviation x ≤ g_up x) ∧
      (∫ x in (0 : ℝ)..1, g_up x ≤ ε) ∧ (-ε ≤ ∫ x in (0 : ℝ)..1, g_lo x) := by
  -- Choose δ = min(ε, 1/2): small enough for integral bounds, large enough to be positive
  set δ := min ε (1/2) with hδ_def
  have hδ_pos : 0 < δ := lt_min hε (by norm_num)
  have hδ_le_ε : δ ≤ ε := min_le_left _ _
  have hδ_le_half : δ ≤ 1/2 := min_le_right _ _
  have hδ_le_one : δ ≤ 1 := le_trans hδ_le_half (by norm_num)
  -- The sandwich functions: core ∘ fract
  refine ⟨fun x => sandwichLoCore δ (Int.fract x),
          fun x => sandwichUpCore δ (Int.fract x), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. g_lo continuous
  · exact continuous_comp_fract (sandwichLoCore_continuous δ hδ_pos)
      (sandwichLoCore_endpoints δ hδ_pos hδ_le_one)
  -- 2. g_up continuous
  · exact continuous_comp_fract (sandwichUpCore_continuous δ hδ_pos)
      (sandwichUpCore_endpoints δ hδ_pos hδ_le_one)
  -- 3. g_lo periodic: fract(x+1) = fract(x)
  · intro x
    show sandwichLoCore δ (Int.fract (x + 1)) = sandwichLoCore δ (Int.fract x)
    have : (x + 1 : ℝ) = x + ↑(1 : ℤ) := by push_cast; ring
    rw [this, Int.fract_add_int]
  -- 4. g_up periodic
  · intro x
    show sandwichUpCore δ (Int.fract (x + 1)) = sandwichUpCore δ (Int.fract x)
    have : (x + 1 : ℝ) = x + ↑(1 : ℤ) := by push_cast; ring
    rw [this, Int.fract_add_int]
  -- 5. g_lo ≤ deviation (bump is nonneg, so subtracting it gives ≤)
  · intro x
    simp only [sandwichLoCore, deviation]
    linarith [div_nonneg (le_max_left (0 : ℝ) (δ - Int.fract x)) hδ_pos.le]
  -- 6. deviation ≤ g_up (bump is nonneg, so adding it gives ≥)
  · intro x
    simp only [sandwichUpCore, deviation]
    linarith [div_nonneg (le_max_left (0 : ℝ) (Int.fract x - (1 - δ))) hδ_pos.le]
  -- 7. ∫₀¹ g_up ≤ ε: integral of bump is δ/2 ≤ ε
  · -- Replace fract by id on [0,1]: fract(x)=x for x∈[0,1) and f(0)=f(1) at x=1
    have h_fract_eq : ∀ x ∈ Set.uIcc (0:ℝ) 1,
        sandwichUpCore δ (Int.fract x) = sandwichUpCore δ x := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      by_cases hx1 : x = 1
      · rw [hx1, Int.fract_one, ← sandwichUpCore_endpoints δ hδ_pos hδ_le_one]
      · rw [Int.fract_eq_self.mpr ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩]
    rw [intervalIntegral.integral_congr h_fract_eq]
    -- Decompose: sandwichUpCore δ x = (1/2 - x) + max(0, x-(1-δ))/δ
    have h_decomp : ∀ x : ℝ, sandwichUpCore δ x = (1/2 - x) + max 0 (x - (1 - δ)) / δ := by
      intro x; unfold sandwichUpCore; ring
    conv_lhs => ext x; rw [h_decomp]
    -- Split integral by linearity
    rw [intervalIntegral.integral_add
      ((continuous_const.sub continuous_id).intervalIntegrable 0 1)
      (((continuous_const.max (continuous_id.sub continuous_const)).div
        continuous_const (fun _ => hδ_pos.ne')).intervalIntegrable 0 1)]
    -- ∫₀¹ (1/2 - x) dx = 0
    have h_lin : ∫ x in (0:ℝ)..1, (1/2 - x : ℝ) = 0 := by
      have h1 : ∫ x in (0:ℝ)..1, (1:ℝ)/2 = 1/2 := by
        rw [intervalIntegral.integral_const]; norm_num
      have h2 : ∫ x in (0:ℝ)..1, (x : ℝ) = 1/2 := by
        rw [integral_id]; norm_num
      linarith [intervalIntegral.integral_sub
        (intervalIntegrable_const) (continuous_id.intervalIntegrable 0 1)]
    -- ∫₀¹ max(0,x-(1-δ))/δ ≤ δ via splitting at 1-δ and bounding by 1
    have h_bump : ∫ x in (0:ℝ)..1, max 0 (x - (1 - δ)) / δ ≤ δ := by
      -- Split: ∫₀¹ = ∫₀^(1-δ) + ∫_(1-δ)^1
      have h_intble : IntervalIntegrable (fun x => max 0 (x - (1 - δ)) / δ)
          MeasureTheory.MeasureSpace.volume 0 1 :=
        (((continuous_const.max (continuous_id.sub continuous_const)).div
          continuous_const (fun _ => hδ_pos.ne')).intervalIntegrable 0 1)
      rw [show (1 : ℝ) = (1 - δ) + δ from by ring,
          ← intervalIntegral.integral_add_adjacent_intervals
            (h_intble.mono_set (by
              constructor <;> simp [Set.uIcc_of_le, min_le_of_left_le, le_max_of_le_right] <;> linarith))
            (h_intble.mono_set (by
              constructor <;> simp [Set.uIcc_of_le, min_le_of_left_le, le_max_of_le_right] <;> linarith))]
      -- On [0, 1-δ]: max(0, x-(1-δ)) = 0 since x ≤ 1-δ
      have h_zero : ∫ x in (0:ℝ)..(1-δ), max 0 (x - (1 - δ)) / δ = 0 := by
        apply intervalIntegral.integral_eq_zero_of_forall_eq_zero
        intro x
        simp only [max_eq_left_iff, sub_nonpos]
        intro hx
        simp [le_of_lt (show x - (1 - δ) ≤ 0 from by linarith), hδ_pos.ne']
      -- On [1-δ, 1]: max(0, x-(1-δ))/δ ≤ 1 (since x-(1-δ) ≤ δ)
      have h_bound : ∫ x in (1-δ)..((1-δ)+δ), max 0 (x - (1 - δ)) / δ ≤ δ := by
        calc ∫ x in (1-δ)..((1-δ)+δ), max 0 (x - (1 - δ)) / δ
            ≤ ∫ x in (1-δ)..((1-δ)+δ), (1 : ℝ) := by
              apply intervalIntegral.integral_mono_on (by linarith)
              · exact h_intble.mono_set (by
                  constructor <;> simp [Set.uIcc_of_le, min_le_of_left_le] <;> linarith)
              · exact intervalIntegrable_const
              · intro x hx
                rw [Set.uIcc_of_le (by linarith : 1 - δ ≤ (1 - δ) + δ)] at hx
                rw [div_le_one hδ_pos]
                exact le_max_of_le_right (by linarith [hx.2])
          _ = 1 * ((1-δ+δ) - (1-δ)) := by rw [intervalIntegral.integral_const]
          _ = δ := by ring
      linarith
    linarith
  -- 8. -ε ≤ ∫₀¹ g_lo: symmetric argument for lower sandwich
  · -- Replace fract by id on [0,1]
    have h_fract_eq : ∀ x ∈ Set.uIcc (0:ℝ) 1,
        sandwichLoCore δ (Int.fract x) = sandwichLoCore δ x := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      by_cases hx1 : x = 1
      · rw [hx1, Int.fract_one, ← sandwichLoCore_endpoints δ hδ_pos hδ_le_one]
      · rw [Int.fract_eq_self.mpr ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩]
    rw [intervalIntegral.integral_congr h_fract_eq]
    -- Decompose: sandwichLoCore δ x = (1/2 - x) - max(0, δ-x)/δ
    have h_decomp : ∀ x : ℝ, sandwichLoCore δ x = (1/2 - x) - max 0 (δ - x) / δ := by
      intro x; unfold sandwichLoCore; ring
    conv_lhs => ext x; rw [h_decomp]
    -- Split integral by linearity
    rw [intervalIntegral.integral_sub
      ((continuous_const.sub continuous_id).intervalIntegrable 0 1)
      (((continuous_const.max (continuous_const.sub continuous_id)).div
        continuous_const (fun _ => hδ_pos.ne')).intervalIntegrable 0 1)]
    -- Reuse: ∫₀¹ (1/2 - x) = 0
    have h_lin : ∫ x in (0:ℝ)..1, (1/2 - x : ℝ) = 0 := by
      have h1 : ∫ x in (0:ℝ)..1, (1:ℝ)/2 = 1/2 := by
        rw [intervalIntegral.integral_const]; norm_num
      have h2 : ∫ x in (0:ℝ)..1, (x : ℝ) = 1/2 := by
        rw [integral_id]; norm_num
      linarith [intervalIntegral.integral_sub
        (intervalIntegrable_const) (continuous_id.intervalIntegrable 0 1)]
    -- ∫₀¹ max(0,δ-x)/δ ≤ δ (symmetric to g_up)
    have h_bump : ∫ x in (0:ℝ)..1, max 0 (δ - x) / δ ≤ δ := by
      have h_intble : IntervalIntegrable (fun x => max 0 (δ - x) / δ)
          MeasureTheory.MeasureSpace.volume 0 1 :=
        (((continuous_const.max (continuous_const.sub continuous_id)).div
          continuous_const (fun _ => hδ_pos.ne')).intervalIntegrable 0 1)
      -- Split: ∫₀¹ = ∫₀^δ + ∫_δ^1
      rw [show (1 : ℝ) = δ + (1 - δ) from by ring,
          ← intervalIntegral.integral_add_adjacent_intervals
            (h_intble.mono_set (by
              constructor <;> simp [Set.uIcc_of_le, min_le_of_left_le, le_max_of_le_right] <;> linarith))
            (h_intble.mono_set (by
              constructor <;> simp [Set.uIcc_of_le, min_le_of_left_le, le_max_of_le_right] <;> linarith))]
      -- On [0, δ]: max(0, δ-x)/δ ≤ 1
      have h_first : ∫ x in (0:ℝ)..δ, max 0 (δ - x) / δ ≤ δ := by
        calc ∫ x in (0:ℝ)..δ, max 0 (δ - x) / δ
            ≤ ∫ x in (0:ℝ)..δ, (1 : ℝ) := by
              apply intervalIntegral.integral_mono_on hδ_pos.le
              · exact h_intble.mono_set (by
                  constructor <;> simp [Set.uIcc_of_le, min_le_of_left_le] <;> linarith)
              · exact intervalIntegrable_const
              · intro x hx
                rw [Set.uIcc_of_le hδ_pos.le] at hx
                rw [div_le_one hδ_pos]
                exact le_max_of_le_right (by linarith [hx.1])
          _ = 1 * (δ - 0) := by rw [intervalIntegral.integral_const]
          _ = δ := by ring
      -- On [δ, 1]: max(0, δ-x) = 0 since δ ≤ x
      have h_second : ∫ x in δ..(δ + (1-δ)), max 0 (δ - x) / δ = 0 := by
        apply intervalIntegral.integral_eq_zero_of_forall_eq_zero
        intro x
        simp only [max_eq_left_iff, sub_nonpos]
        intro hx
        simp [le_of_lt (show δ - x ≤ 0 from by linarith), hδ_pos.ne']
      linarith
    -- Combine: 0 - bump ≥ -δ ≥ -ε
    linarith

/-- **For irrational α, (1/n) · S(α,n) → 0.**
    Proof: sandwich deviation between continuous periodic bounds g_lo ≤ deviation ≤ g_up
    with ∫g_up ≤ ε/2 and ∫g_lo ≥ -ε/2, apply `weyl_equidist_continuous` to both,
    then squeeze: avg(g_lo) ≤ innerSum/n ≤ avg(g_up) and both sides → ≈ 0. -/
theorem weyl_fract_average_zero (α : ℝ) (hα : Irrational α) :
    Filter.Tendsto (fun n : ℕ => innerSum α n / n) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g_lo, g_up, hlo_cont, hup_cont, hlo_per, hup_per,
          hlo_le, hup_ge, hup_int, hlo_int⟩ :=
    deviation_sandwich (ε / 2) (by linarith)
  have h_up := weyl_equidist_continuous α hα g_up hup_cont hup_per
  have h_lo := weyl_equidist_continuous α hα g_lo hlo_cont hlo_per
  rw [Metric.tendsto_atTop] at h_up h_lo
  obtain ⟨N₁, hN₁⟩ := h_up (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := h_lo (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) hN
  rw [Real.dist_eq, sub_zero]
  -- Sum ordering: Σg_lo ≤ innerSum ≤ Σg_up
  have h_dev_le_up : innerSum α N ≤ ∑ n ∈ range N, g_up (α * (↑n + 1)) := by
    unfold innerSum; exact Finset.sum_le_sum (fun k _ => hup_ge _)
  have h_lo_le_dev : ∑ n ∈ range N, g_lo (α * (↑n + 1)) ≤ innerSum α N := by
    unfold innerSum; exact Finset.sum_le_sum (fun k _ => hlo_le _)
  -- Divide by N (nonneg)
  have h_upper : innerSum α N / ↑N ≤
      (∑ n ∈ range N, g_up (α * (↑n + 1))) / ↑N :=
    div_le_div_of_nonneg_right h_dev_le_up (Nat.cast_nonneg _)
  have h_lower : (∑ n ∈ range N, g_lo (α * (↑n + 1))) / ↑N ≤
      innerSum α N / ↑N :=
    div_le_div_of_nonneg_right h_lo_le_dev (Nat.cast_nonneg _)
  -- avg(g_up) < ∫g_up + ε/2 ≤ ε
  have h_avg_up : (∑ n ∈ range N, g_up (α * (↑n + 1))) / ↑N < ε := by
    have h := hN₁ N hN1; rw [Real.dist_eq] at h
    linarith [(abs_lt.mp h).2, hup_int]
  -- avg(g_lo) > ∫g_lo - ε/2 ≥ -ε
  have h_avg_lo : -(ε : ℝ) < (∑ n ∈ range N, g_lo (α * (↑n + 1))) / ↑N := by
    have h := hN₂ N hN2; rw [Real.dist_eq] at h
    linarith [(abs_lt.mp h).1, hlo_int]
  -- Squeeze: -ε < avg(g_lo) ≤ innerSum/N ≤ avg(g_up) < ε
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

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
