/-
  Truncation Error Bound for the Generalized Triangular Reciprocal Series
  (triangular-reciprocals-oq-02-oq-04)

  Parent: `Proofs/TriangularReciprocalsOQ02.lean` (slug `triangular-reciprocals-oq-02`)
  proves the closed form

      ∑_{n=1}^∞ 1/(n(n+k)) = H_k / k        (k ≥ 1)

  and, en route, the partial-sum closed form

      ∑_{n=1}^N 1/(n(n+k)) = (1/k)(H_k - (H_{N+k} - H_N)).

  This file answers the parent's fourth open question:

      "Quantify the rate of convergence: the closed form gives
         |∑_{n=1}^∞ 1/(n(n+k)) - S_N(k)| = (1/k)(H_{N+k} - H_N) ≤ 1/(N+1)
       uniformly in k — formalize this as a Mathlib-style truncation error
       bound for the partial sums."

  Mathematical content.
    The truncation error is exactly (1/k)(H_{N+k} - H_N), an immediate algebraic
    consequence of the parent's partial-sum closed form. The new ingredient is the
    *uniform* bound
        H_{N+k} - H_N = ∑_{i=N+1}^{N+k} 1/i ≤ k/(N+1)
    (each of the k tail terms is ≤ 1/(N+1)), proved here by induction on k. Dividing
    by k cancels the k completely, leaving the ceiling 1/(N+1) which does NOT depend
    on k. That k-independence is the headline.

  Results.
    * `harmonic_diff_nonneg`        : 0 ≤ H_{N+k} - H_N
    * `harmonic_diff_le`            : H_{N+k} - H_N ≤ k/(N+1)          (core new lemma)
    * `truncation_error_eq`         : H_k/k - S_N = (1/k)(H_{N+k} - H_N)
    * `truncation_error_nonneg`     : 0 ≤ H_k/k - S_N
    * `truncation_error_le`         : H_k/k - S_N ≤ 1/(N+1)
    * `truncation_error_abs`        : |H_k/k - S_N| ≤ 1/(N+1)
    * `truncation_error_uniform`    : the bound 1/(N+1) holds for every k ≥ 1
    * `truncation_error_tsum_abs`   : the same bound against the genuine ∑' value

  Status: verified, 0 axioms (depends only on Mathlib + the parent module).
-/
import Mathlib
import Proofs.TriangularReciprocalsOQ02

namespace TriangularReciprocalsOQ02OQ04

open Finset BigOperators Filter Topology Real
open TriangularReciprocalsHarmonic

-- ═══════════════════════════════════════════════════
-- Harmonic tail difference: nonnegativity and the uniform k/(N+1) bound
-- ═══════════════════════════════════════════════════

/-- The harmonic tail difference is nonnegative: H_{N+k} ≥ H_N. -/
theorem harmonic_diff_nonneg (N k : ℕ) :
    (0 : ℝ) ≤ (harmonic (N + k) : ℝ) - (harmonic N : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (harmonic (N + (k + 1)) : ℝ) =
        (harmonic (N + k) : ℝ) + 1 / ((N : ℝ) + (k : ℝ) + 1) := by
      have h1 : N + (k + 1) = (N + k) + 1 := rfl
      rw [h1, harmonic_succ]; push_cast; ring
    rw [hstep]
    have hpos : (0 : ℝ) ≤ 1 / ((N : ℝ) + (k : ℝ) + 1) := by positivity
    linarith [ih]

/-- **Uniform tail bound.** Each of the k harmonic terms H_{N+1}, …, H_{N+k}/… is at
    most 1/(N+1), so

        H_{N+k} - H_N ≤ k/(N+1).

    Proved by induction on k: the inductive step adds one term 1/(N+k+1) ≤ 1/(N+1). -/
theorem harmonic_diff_le (N k : ℕ) :
    (harmonic (N + k) : ℝ) - (harmonic N : ℝ) ≤ (k : ℝ) / ((N : ℝ) + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (harmonic (N + (k + 1)) : ℝ) =
        (harmonic (N + k) : ℝ) + 1 / ((N : ℝ) + (k : ℝ) + 1) := by
      have h1 : N + (k + 1) = (N + k) + 1 := rfl
      rw [h1, harmonic_succ]; push_cast; ring
    have hterm : (1 : ℝ) / ((N : ℝ) + (k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
    rw [hstep]
    push_cast
    rw [add_div]
    linarith [ih, hterm]

-- ═══════════════════════════════════════════════════
-- Truncation error identity and bound (partial sum in Icc form)
-- ═══════════════════════════════════════════════════

/-- **Exact truncation error.** The difference between the closed-form value H_k/k and
    the N-term partial sum is exactly (1/k)(H_{N+k} - H_N). Immediate from the parent's
    `partial_sum_closed_form`. -/
theorem truncation_error_eq (N k : ℕ) (hk : 0 < k) :
    (harmonic k : ℝ) / (k : ℝ) -
        ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + ↑k)) =
      (1 / (k : ℝ)) * ((harmonic (N + k) : ℝ) - (harmonic N : ℝ)) := by
  rw [partial_sum_closed_form N k hk]
  ring

/-- The partial sum underestimates the true value: H_k/k - S_N ≥ 0. -/
theorem truncation_error_nonneg (N k : ℕ) (hk : 0 < k) :
    (0 : ℝ) ≤ (harmonic k : ℝ) / (k : ℝ) -
        ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + ↑k)) := by
  rw [truncation_error_eq N k hk]
  apply mul_nonneg
  · positivity
  · exact harmonic_diff_nonneg N k

/-- **Uniform truncation error bound** (signed form): for every k ≥ 1,

        H_k/k - S_N(k) ≤ 1/(N+1),

    with the right-hand side independent of k. -/
theorem truncation_error_le (N k : ℕ) (hk : 0 < k) :
    (harmonic k : ℝ) / (k : ℝ) -
        ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + ↑k)) ≤
      1 / ((N : ℝ) + 1) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [truncation_error_eq N k hk, one_div_mul_eq_div, div_le_iff₀ hk0]
  calc (harmonic (N + k) : ℝ) - (harmonic N : ℝ)
      ≤ (k : ℝ) / ((N : ℝ) + 1) := harmonic_diff_le N k
    _ = 1 / ((N : ℝ) + 1) * (k : ℝ) := by ring

/-- **Uniform truncation error bound** (absolute-value form): for every k ≥ 1,

        |H_k/k - S_N(k)| ≤ 1/(N+1). -/
theorem truncation_error_abs (N k : ℕ) (hk : 0 < k) :
    |(harmonic k : ℝ) / (k : ℝ) -
        ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + ↑k))| ≤
      1 / ((N : ℝ) + 1) := by
  rw [abs_of_nonneg (truncation_error_nonneg N k hk)]
  exact truncation_error_le N k hk

/-- **Uniformity, made explicit.** The single ceiling `1/(N+1)` controls the truncation
    error simultaneously for *all* gap parameters k ≥ 1. This is the crux of the open
    question: dividing the tail (1/k)(H_{N+k} - H_N) by k cancels every dependence on k. -/
theorem truncation_error_uniform (N : ℕ) :
    ∀ k : ℕ, 0 < k →
      |(harmonic k : ℝ) / (k : ℝ) -
          ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + ↑k))| ≤
        1 / ((N : ℝ) + 1) :=
  fun k hk => truncation_error_abs N k hk

-- ═══════════════════════════════════════════════════
-- Truncation error against the genuine infinite series (∑' form)
-- ═══════════════════════════════════════════════════

/-- Re-index the `range N` partial sum (used by the parent's `HasSum`/`tsum`) into the
    `Icc 1 N` partial sum. Transferred from the parent's `h_range_to_Icc`. -/
theorem range_sum_eq_Icc (N k : ℕ) :
    ∑ i ∈ Finset.range N,
        (1 : ℝ) / (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + ↑k)) =
      ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + ↑k)) := by
  rw [show (Finset.Icc 1 N) = Finset.Ico 1 (N + 1) from
        (Finset.Ico_succ_right_eq_Icc (a := 1) (b := N)).symm,
      ← Nat.Ico_zero_eq_range]
  have key := Finset.sum_Ico_add'
    (fun m : ℕ => (1 : ℝ) / ((m : ℝ) * ((m : ℝ) + ↑k))) 0 N (c := 1)
  simp only [zero_add] at key
  rw [← key]

/-- **Truncation error against the true sum.** The N-th partial sum of the actual
    infinite series ∑' 1/((n+1)((n+1)+k)) differs from its value by at most 1/(N+1),
    uniformly in k. This is the open question phrased directly in terms of the genuine
    `tsum`, by combining the parent's closed form with `truncation_error_abs`. -/
theorem truncation_error_tsum_abs (N k : ℕ) (hk : 0 < k) :
    |(∑' n : ℕ, (1 : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + ↑k))) -
        ∑ i ∈ Finset.range N,
          (1 : ℝ) / (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + ↑k))| ≤
      1 / ((N : ℝ) + 1) := by
  rw [generalized_triangular_reciprocals_tsum k hk, range_sum_eq_Icc N k]
  exact truncation_error_abs N k hk

end TriangularReciprocalsOQ02OQ04
