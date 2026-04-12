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

**Remaining sorries** (well-scoped, independently provable):
- `equidist_approx`: density of trig polys via `span_fourier_closure_eq_top`
- `deviation_sandwich`: piecewise linear continuous sandwich of deviation

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
  sorry

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
    -- Need: ∀ ε > 0, ∃ δ > 0, |y-x| < δ → |f(fract(y)) - f(0)| < ε
    -- Key: fract(y) is near 0 (right of x) or near 1 (left of x), and f(0) = f(1)
    sorry
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
  · -- On [0,1], fract(x) = x a.e., so integral equals ∫₀¹ sandwichUpCore δ.
    -- sandwichUpCore = deviation + bump_up, ∫deviation = 0, ∫bump_up = δ/2 ≤ ε.
    sorry
  -- 8. -ε ≤ ∫₀¹ g_lo: integral of bump is -δ/2 ≥ -ε
  · sorry

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
