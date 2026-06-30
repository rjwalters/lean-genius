/-
  # The Geometric Exponential Sum Bound (Pólya–Vinogradov ingredient)

  The companion file `BoundedPrimeGapsOQ04OQ01` sets up the Pólya–Vinogradov
  inequality `|∑_{n} χ(n)| ≤ √q·log q` for Dirichlet characters, leaving four
  analytic `sorry`s. Its key technical ingredient — and the only one that is a
  clean, self-contained classical estimate — is the bound on a **partial geometric
  sum of an exponential with unit-modulus ratio**:

      |∑_{n=M+1}^{M+N} e^{2πiθn}| ≤ 1 / |sin(πθ)|    (θ ∉ ℤ).

  This file proves exactly that, fully machine-checked. (The companion file is a
  work-in-progress that does not currently parse against Mathlib — it uses the
  retired `∑ x in s` syntax — so this entry re-establishes the small set of
  supporting lemmas and the main bound from scratch, with modern syntax.)

  The estimate is the heart of Pólya–Vinogradov: writing the character sum via its
  Gauss-sum Fourier expansion turns it into a combination of such exponential sums,
  and `1/|sin(πθ)|` is precisely the factor that the cotangent sum then aggregates.

  ## Results
  * `norm_one_sub_exp_two_pi_I` : `|1 − e^{2πiθ}| = 2|sin(πθ)|` (the chord-length
    identity on the unit circle).
  * `geom_partial_sum_bound` : the headline `|∑_{M+1}^{M+N} e^{2πiθn}| ≤ 1/|sin(πθ)|`.
  * `geom_partial_sum_bound_zero` : the `M = 0` special case over `Icc 1 N`.

  ## Proof
  With `z = e^{2πiθ}` on the unit circle, the partial sum is
  `z^{M+1}·∑_{k<N} z^k = z^{M+1}·(z^N − 1)/(z − 1)`. Then `|z^{M+1}| = 1`,
  `|z^N − 1| ≤ 2` (triangle inequality), and `|z − 1| = 2|sin(πθ)|` (chord length),
  giving `2 / (2|sin(πθ)|) = 1/|sin(πθ)|`.

  Tags: analytic-number-theory, character-sums, polya-vinogradov, geometric-sum,
        exponential-sum
-/
import Mathlib

namespace BoundedPrimeGapsOQ04OQ01WIP01

open Finset Complex Real

/-- `sin(πθ) ≠ 0` when `θ` is not an integer. -/
lemma sin_pi_mul_ne_zero (θ : ℝ) (hθ : ∀ k : ℤ, θ ≠ ↑k) :
    Real.sin (π * θ) ≠ 0 := by
  intro h
  rw [Real.sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hπ : (π : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  rw [mul_comm] at hk
  exact hθ k (mul_left_cancel₀ hπ hk).symm

/-- `|1 − z^n| ≤ 2` when `|z| = 1` (triangle inequality on the unit circle). -/
lemma norm_one_sub_pow_le_two (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖(1 : ℂ) - z ^ n‖ ≤ 2 := by
  calc ‖(1 : ℂ) - z ^ n‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ n‖ := norm_sub_le _ _
    _ = 1 + ‖z ^ n‖ := by rw [norm_one]
    _ = 1 + 1 := by rw [norm_pow, hz, one_pow]
    _ = 2 := by ring

/-- The chord-length identity `|1 − e^{2πiθ}| = 2|sin(πθ)|`. -/
lemma norm_one_sub_exp_two_pi_I (θ : ℝ) :
    ‖(1 : ℂ) - exp (2 * ↑π * I * ↑θ)‖ = 2 * |Real.sin (π * θ)| := by
  have harg : (2 : ℂ) * ↑π * I * ↑θ = ↑(2 * π * θ) * I := by push_cast; ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hdiff : (1 : ℂ) - (↑(Real.cos (2 * π * θ)) + ↑(Real.sin (2 * π * θ)) * I) =
      ↑(1 - Real.cos (2 * π * θ)) + ↑(-Real.sin (2 * π * θ)) * I := by push_cast; ring
  rw [hdiff, Complex.norm_add_mul_I]
  have h_sq : (1 - Real.cos (2 * π * θ)) ^ 2 + (-Real.sin (2 * π * θ)) ^ 2 =
      (2 * |Real.sin (π * θ)|) ^ 2 := by
    rw [mul_pow, sq_abs, neg_sq]
    have h1 := Real.sin_sq_add_cos_sq (2 * π * θ)
    have h2 := Real.cos_two_mul (π * θ)
    have h2arg : 2 * (π * θ) = 2 * π * θ := by ring
    rw [h2arg] at h2
    have h3 := Real.sin_sq_add_cos_sq (π * θ)
    linear_combination h1 - 2 * h2 - 4 * h3
  rw [h_sq, Real.sqrt_sq (by positivity)]

/-- **Geometric exponential sum bound.** For `θ ∉ ℤ`,
    `|∑_{n=M+1}^{M+N} e^{2πiθn}| ≤ 1/|sin(πθ)|`. The key estimate behind the
    Pólya–Vinogradov inequality. -/
theorem geom_partial_sum_bound (θ : ℝ) (hθ : ∀ k : ℤ, θ ≠ ↑k) (M N : ℕ) :
    ‖∑ n ∈ Finset.Icc (M + 1) (M + N), exp (2 * ↑π * I * ↑θ * (n : ℂ))‖ ≤
    1 / |Real.sin (π * θ)| := by
  set z : ℂ := exp (2 * ↑π * I * ↑θ) with hz_def
  -- `|z| = 1`.
  have hzI : (2 : ℂ) * ↑π * I * ↑θ = ↑(2 * π * θ) * I := by push_cast; ring
  have hznorm1 : ‖z‖ = 1 := by rw [hz_def, hzI]; exact norm_exp_ofReal_mul_I (2 * π * θ)
  -- `sin(πθ) ≠ 0` and `|1 − z| = 2|sin(πθ)|`.
  have hsin : Real.sin (π * θ) ≠ 0 := sin_pi_mul_ne_zero θ hθ
  have h1z : ‖(1 : ℂ) - z‖ = 2 * |Real.sin (π * θ)| := by
    rw [hz_def]; exact norm_one_sub_exp_two_pi_I θ
  -- Hence `z ≠ 1`.
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at h1z
    exact hsin (abs_eq_zero.mp (by linarith))
  -- Each summand is `z^n`.
  have hpow : ∀ n : ℕ, exp (2 * ↑π * I * ↑θ * (n : ℂ)) = z ^ n := by
    intro n
    rw [hz_def, ← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [hpow]
  -- Geometric partial sum: `∑_{n=M+1}^{M+N} z^n = z^{M+1}·∑_{k<N} z^k`.
  have hgeom : ∑ n ∈ Finset.Icc (M + 1) (M + N), z ^ n
      = z ^ (M + 1) * ∑ k ∈ Finset.range N, z ^ k := by
    rw [← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one,
      Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr
    · congr 1; omega
    · intro k _; rw [pow_add]
  have h1z' : ‖z - 1‖ = 2 * |Real.sin (π * θ)| := by rw [norm_sub_rev]; exact h1z
  rw [hgeom, geom_sum_eq hz1, norm_mul, norm_pow, hznorm1, one_pow, one_mul, norm_div, h1z']
  -- Combine `|z^N − 1| ≤ 2` with `|z − 1| = 2|sin(πθ)|`.
  have hsinpos : (0 : ℝ) < |Real.sin (π * θ)| := abs_pos.mpr hsin
  have hne : |Real.sin (π * θ)| ≠ 0 := ne_of_gt hsinpos
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    rw [norm_sub_rev]; exact norm_one_sub_pow_le_two z hznorm1 N
  calc ‖z ^ N - 1‖ / (2 * |Real.sin (π * θ)|)
      ≤ 2 / (2 * |Real.sin (π * θ)|) := by gcongr
    _ = 1 / |Real.sin (π * θ)| := by field_simp

/-- The `M = 0` special case: `|∑_{n=1}^{N} e^{2πiθn}| ≤ 1/|sin(πθ)|`. -/
theorem geom_partial_sum_bound_zero (θ : ℝ) (hθ : ∀ k : ℤ, θ ≠ ↑k) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, exp (2 * ↑π * I * ↑θ * (n : ℂ))‖ ≤
    1 / |Real.sin (π * θ)| := by
  simpa using geom_partial_sum_bound θ hθ 0 N

end BoundedPrimeGapsOQ04OQ01WIP01
