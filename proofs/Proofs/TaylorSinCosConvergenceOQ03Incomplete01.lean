/-
# Completing the alternating Taylor-remainder bounds for sin/cos (OQ-03 incomplete-01)

The parent entry **taylor-sincos-convergence-oq-03** develops sharper (alternating-
series) remainder bounds for the Taylor series of `sin` and `cos`, but leaves three
`sorry`s: the general **alternating-series estimation** `alternating_tail_bound`,
and its two applications `sin_alternating_remainder` / `cos_alternating_remainder`.

This file discharges that mathematics, self-contained and axiom-free, using
Mathlib's `alternating_series_error_bound` together with `Real.cos_eq_tsum` /
`Real.sin_eq_tsum`:

  * `alternating_tail_bound` — for an antitone summable `a`, the alternating tail
    from index `n` is bounded by `a n` (Leibniz estimation), via the
    tail-decomposition `∑' k, f(k+n) = (∑' f) − ∑_{i<n} f i`.
  * `cos_alternating_remainder` — for `|x| ≤ 1`, the cosine partial sum through
    `x^{2n−2}/(2n−2)!` has error `≤ |x|^{2n}/(2n)!`. (Even powers, so this holds
    for both signs of `x`.)
  * `sin_alternating_remainder` — for `0 ≤ x ≤ 1`, the analogous sine bound
    `≤ |x|^{2n+1}/(2n+1)!`.

The restriction `|x| ≤ 1` is exactly where the term sequence is monotone, the
hypothesis the alternating-series estimation requires; this is the correct domain
for the alternating (as opposed to Lagrange) sharpening. Self-contained: the term
definitions are reproduced from the parent (which still carries `sorry`s, so
importing it is undesirable).
-/
import Mathlib

namespace TaylorSinCosConvergenceOQ03Incomplete01

open Finset Filter

/- ## Part I: the alternating-series estimation -/

/-- **Alternating-series estimation (Leibniz).** For a non-negative-valued (here
derived), antitone, summable `a`, the alternating tail starting at index `n` has
norm at most `a n`. This is the parent's `alternating_tail_bound`, proved via
Mathlib's `alternating_series_error_bound` and the tail decomposition. -/
theorem alternating_tail_bound {a : ℕ → ℝ} (ha_dec : Antitone a) (ha_sum : Summable a)
    (n : ℕ) : ‖∑' k, (-1 : ℝ) ^ (k + n) * a (k + n)‖ ≤ a n := by
  have ha_nn : ∀ i, 0 ≤ a i := fun i => ha_dec.le_of_tendsto ha_sum.tendsto_atTop_zero i
  have hg : Summable (fun i => (-1 : ℝ) ^ i * a i) := by
    apply Summable.of_norm
    have : (fun i => ‖(-1 : ℝ) ^ i * a i‖) = a := by
      funext i; rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Real.norm_eq_abs, abs_of_nonneg (ha_nn i)]
    rwa [this]
  have hsplit := hg.sum_add_tsum_nat_add n
  have hreindex : ∑' k, (-1 : ℝ) ^ (k + n) * a (k + n)
      = (∑' i, (-1 : ℝ) ^ i * a i) - ∑ i ∈ range n, (-1 : ℝ) ^ i * a i := by
    rw [eq_sub_iff_add_eq, add_comm]; exact hsplit
  rw [hreindex, Real.norm_eq_abs]
  exact alternating_series_error_bound a ha_dec ha_sum n

/- ## Part II: sin/cos term magnitudes (reproduced from the parent) -/

/-- `|x|^{2k+1}/(2k+1)!`, the magnitude of the `k`-th sine term. -/
noncomputable def sinTermAbs (x : ℝ) (k : ℕ) : ℝ :=
  |x| ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)

/-- `|x|^{2k}/(2k)!`, the magnitude of the `k`-th cosine term. -/
noncomputable def cosTermAbs (x : ℝ) (k : ℕ) : ℝ :=
  |x| ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)

theorem cosTermAbs_antitone (x : ℝ) (hx : |x| ≤ 1) : Antitone (cosTermAbs x) := by
  apply antitone_nat_of_succ_le
  intro k
  simp only [cosTermAbs]
  calc (|x| ^ (2 * (k + 1)) : ℝ) / ↑(Nat.factorial (2 * (k + 1)))
      ≤ |x| ^ (2 * k) / ↑(Nat.factorial (2 * (k + 1))) := by
        apply div_le_div_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg x) hx (by omega))
        exact Nat.cast_nonneg' _
    _ ≤ |x| ^ (2 * k) / ↑(Nat.factorial (2 * k)) := by
        apply div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg x) _)
          (Nat.cast_pos.mpr (Nat.factorial_pos _))
        exact Nat.cast_le.mpr (Nat.factorial_le (by omega))

theorem sinTermAbs_antitone (x : ℝ) (hx : |x| ≤ 1) : Antitone (sinTermAbs x) := by
  apply antitone_nat_of_succ_le
  intro k
  simp only [sinTermAbs]
  calc (|x| ^ (2 * (k + 1) + 1) : ℝ) / ↑(Nat.factorial (2 * (k + 1) + 1))
      ≤ |x| ^ (2 * k + 1) / ↑(Nat.factorial (2 * (k + 1) + 1)) := by
        apply div_le_div_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg x) hx (by omega))
        exact Nat.cast_nonneg' _
    _ ≤ |x| ^ (2 * k + 1) / ↑(Nat.factorial (2 * k + 1)) := by
        apply div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg x) _)
          (Nat.cast_pos.mpr (Nat.factorial_pos _))
        exact Nat.cast_le.mpr (Nat.factorial_le (by omega))

theorem cosTermAbs_summable (x : ℝ) : Summable (cosTermAbs x) :=
  (Real.summable_pow_div_factorial |x|).comp_injective
    (by intro a b h; dsimp only at h; omega : Function.Injective (2 * ·))

theorem sinTermAbs_summable (x : ℝ) : Summable (sinTermAbs x) :=
  (Real.summable_pow_div_factorial |x|).comp_injective
    (by intro a b h; dsimp only at h; omega : Function.Injective (fun k => 2 * k + 1))

/- ## Part III: the alternating remainder bounds -/

/-- **Cosine alternating remainder.** For `|x| ≤ 1`, the partial cosine sum through
`x^{2n−2}/(2n−2)!` has error at most `|x|^{2n}/(2n)!`. Cosine has even powers, so
`x^{2k} = |x|^{2k}` and the bound holds for either sign of `x`. -/
theorem cos_alternating_remainder {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    ‖Real.cos x - ∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)‖
      ≤ cosTermAbs x n := by
  have hterm : ∀ k : ℕ,
      (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) = (-1 : ℝ) ^ k * cosTermAbs x k := by
    intro k
    have hpow : x ^ (2 * k) = |x| ^ (2 * k) := by rw [pow_mul, pow_mul, sq_abs]
    simp only [cosTermAbs, hpow]; ring
  have hsum : Real.cos x = ∑' k, (-1 : ℝ) ^ k * cosTermAbs x k := by
    rw [Real.cos_eq_tsum]; exact tsum_congr hterm
  have hpartial : (∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))
      = ∑ k ∈ range n, (-1 : ℝ) ^ k * cosTermAbs x k := Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum, hpartial, Real.norm_eq_abs]
  exact alternating_series_error_bound (cosTermAbs x) (cosTermAbs_antitone x hx)
    (cosTermAbs_summable x) n

/-- **Sine alternating remainder.** For `0 ≤ x ≤ 1`, the partial sine sum through
`x^{2n−1}/(2n−1)!` has error at most `|x|^{2n+1}/(2n+1)!`. (For `x ≥ 0`,
`x^{2k+1} = |x|^{2k+1}`; the general `|x| ≤ 1` case follows by oddness of `sin`.) -/
theorem sin_alternating_remainder {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    ‖Real.sin x - ∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)‖
      ≤ sinTermAbs x n := by
  have habs : |x| = x := abs_of_nonneg hx0
  have hterm : ∀ k : ℕ,
      (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)
        = (-1 : ℝ) ^ k * sinTermAbs x k := by
    intro k; simp only [sinTermAbs, habs]; ring
  have hsum : Real.sin x = ∑' k, (-1 : ℝ) ^ k * sinTermAbs x k := by
    rw [Real.sin_eq_tsum]; exact tsum_congr hterm
  have hpartial : (∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ))
      = ∑ k ∈ range n, (-1 : ℝ) ^ k * sinTermAbs x k := Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum, hpartial, Real.norm_eq_abs]
  exact alternating_series_error_bound (sinTermAbs x) (sinTermAbs_antitone x (by rw [habs]; exact hx1))
    (sinTermAbs_summable x) n

end TaylorSinCosConvergenceOQ03Incomplete01
