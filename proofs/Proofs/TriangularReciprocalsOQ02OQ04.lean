/-
  Uniform Truncation Error Bound for Generalized Triangular Reciprocals

  Parent: `triangular-reciprocals-oq-02` (slug `TriangularReciprocalsOQ02.lean`),
  which proves the closed form
      ∑_{n=1}^∞ 1/(n(n+k)) = H_k / k          (H_k = harmonic k).

  This file answers the parent's open question #4:

    "Quantify the rate of convergence: the closed form gives
        |∑_{n=1}^∞ 1/(n(n+k)) − S_N(k)| = (1/k)(H_{N+k} − H_N) ≤ 1/(N+1)
     uniformly in k — formalize this as a Mathlib-style truncation error bound."

  Main results:
    * `truncation_error_eq`  : the tail (total − partial over `range N`) equals
                               exactly (1/k)(H_{N+k} − H_N).
    * `truncation_error_le`  : that tail is ≤ 1/(N+1), a bound **independent of k**
                               (hence uniform in k).
    * `truncation_error_ge`  : that tail is ≥ 1/(N+k), so the 1/(N+1) bound is
                               essentially sharp (both sides ~ 1/N for fixed k).
    * `truncation_error_abs` : |S_N − total| ≤ 1/(N+1).

  The heart is the elementary harmonic-block estimate
      H_{N+k} − H_N = ∑_{i=N+1}^{N+k} 1/i ,
  each of the k terms lying in [1/(N+k), 1/(N+1)], giving
      k/(N+k) ≤ H_{N+k} − H_N ≤ k/(N+1).

  Status: all lemmas closed, no sorries, no extra axioms.
-/
import Mathlib
import Proofs.TriangularReciprocalsOQ02

namespace TriangularReciprocalsTruncation

open Finset BigOperators Filter Topology Real
open TriangularReciprocalsHarmonic

/-- The summand of the generalized triangular series, indexed so that `n + 1`
    ranges over 1, 2, 3, … (matching the parent's convention). -/
private noncomputable def f (k : ℕ) (n : ℕ) : ℝ :=
  (1 : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + (k : ℝ)))

-- ═══════════════════════════════════════════════════
-- Harmonic numbers as real finite sums
-- ═══════════════════════════════════════════════════

/-- `(harmonic m : ℝ)` written as a finite real sum over `Icc 1 m`. -/
theorem harmonic_real_eq (m : ℕ) :
    (harmonic m : ℝ) = ∑ i ∈ Finset.Icc 1 m, (1 : ℝ) / (i : ℝ) := by
  have h := harmonic_eq_sum_Icc (n := m)
  have hR : ((harmonic m : ℚ) : ℝ) = (((∑ i ∈ Finset.Icc 1 m, (↑i)⁻¹ : ℚ) : ℝ)) := by
    exact_mod_cast congrArg (Rat.cast : ℚ → ℝ) h
  rw [hR]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [one_div]

/-- Harmonic difference as a block sum: for `a ≤ b`,
    `H_b − H_a = ∑_{i=a+1}^{b} 1/i`. -/
theorem harmonic_sub {a b : ℕ} (hab : a ≤ b) :
    (harmonic b : ℝ) - (harmonic a : ℝ) =
      ∑ i ∈ Finset.Icc (a + 1) b, (1 : ℝ) / (i : ℝ) := by
  rw [harmonic_real_eq b, harmonic_real_eq a]
  rw [show Finset.Icc 1 b = Finset.Ico 1 (b + 1) from
        (Finset.Ico_succ_right_eq_Icc (a := 1) (b := b)).symm,
      show Finset.Icc 1 a = Finset.Ico 1 (a + 1) from
        (Finset.Ico_succ_right_eq_Icc (a := 1) (b := a)).symm,
      show Finset.Icc (a + 1) b = Finset.Ico (a + 1) (b + 1) from
        (Finset.Ico_succ_right_eq_Icc (a := a + 1) (b := b)).symm]
  have h_cons :
      (∑ i ∈ Finset.Ico 1 (a + 1), (1 : ℝ) / (i : ℝ)) +
        (∑ i ∈ Finset.Ico (a + 1) (b + 1), (1 : ℝ) / (i : ℝ)) =
          ∑ i ∈ Finset.Ico 1 (b + 1), (1 : ℝ) / (i : ℝ) :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  linarith [h_cons]

-- ═══════════════════════════════════════════════════
-- Two-sided block estimate for H_{N+k} − H_N
-- ═══════════════════════════════════════════════════

/-- Upper estimate: `H_{N+k} − H_N ≤ k/(N+1)` (each of the k terms is ≤ 1/(N+1)). -/
theorem harmonic_diff_le (N k : ℕ) :
    (harmonic (N + k) : ℝ) - (harmonic N : ℝ) ≤ (k : ℝ) / ((N : ℝ) + 1) := by
  rw [harmonic_sub (show N ≤ N + k by omega)]
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hbound :
      ∑ i ∈ Finset.Icc (N + 1) (N + k), (1 : ℝ) / (i : ℝ) ≤
        ∑ _i ∈ Finset.Icc (N + 1) (N + k), (1 : ℝ) / ((N : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi1 : (N : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hi.1
    exact one_div_le_one_div_of_le hN1 hi1
  refine hbound.trans ?_
  rw [Finset.sum_const, Nat.card_Icc]
  have hcard : (N + k + 1) - (N + 1) = k := by omega
  rw [hcard, nsmul_eq_mul]
  rw [mul_one_div]

/-- Lower estimate: `H_{N+k} − H_N ≥ k/(N+k)` (each of the k terms is ≥ 1/(N+k)). -/
theorem harmonic_diff_ge (N k : ℕ) (hk : 0 < k) :
    (k : ℝ) / ((N : ℝ) + (k : ℝ)) ≤ (harmonic (N + k) : ℝ) - (harmonic N : ℝ) := by
  rw [harmonic_sub (show N ≤ N + k by omega)]
  have hNk : (0 : ℝ) < (N : ℝ) + (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    positivity
  have hbound :
      ∑ _i ∈ Finset.Icc (N + 1) (N + k), (1 : ℝ) / ((N : ℝ) + (k : ℝ)) ≤
        ∑ i ∈ Finset.Icc (N + 1) (N + k), (1 : ℝ) / (i : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hpos : (0 : ℝ) < (i : ℝ) := by
      have : (1 : ℕ) ≤ i := by omega
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hiNk : (i : ℝ) ≤ (N : ℝ) + (k : ℝ) := by
      have : i ≤ N + k := hi.2
      have := (Nat.cast_le (α := ℝ)).mpr this
      push_cast at this ⊢
      linarith
    exact one_div_le_one_div_of_le hpos hiNk
  refine le_trans ?_ hbound
  rw [Finset.sum_const, Nat.card_Icc]
  have hcard : (N + k + 1) - (N + 1) = k := by omega
  rw [hcard, nsmul_eq_mul]
  rw [mul_one_div]

-- ═══════════════════════════════════════════════════
-- Partial sum over `range N` (lifted from parent's closed form)
-- ═══════════════════════════════════════════════════

/-- Partial sum of `f k` over `range N` in closed form:
    `∑_{i<N} f k i = (1/k)(H_k − (H_{N+k} − H_N))`. -/
theorem range_partial (N k : ℕ) (hk : 0 < k) :
    ∑ i ∈ Finset.range N, f k i =
      (1 / (k : ℝ)) *
        ((harmonic k : ℝ) - ((harmonic (N + k) : ℝ) - (harmonic N : ℝ))) := by
  -- Convert the `range`-indexed sum into the `Icc 1 N`-form used by the parent.
  have h_range_to_Icc :
      ∑ i ∈ Finset.range N, f k i =
        ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + ↑k)) := by
    unfold f
    rw [show (Finset.Icc 1 N) = Finset.Ico 1 (N + 1) from
          (Finset.Ico_succ_right_eq_Icc (a := 1) (b := N)).symm,
        ← Nat.Ico_zero_eq_range]
    have key := Finset.sum_Ico_add'
      (fun m : ℕ => (1 : ℝ) / ((m : ℝ) * ((m : ℝ) + ↑k))) 0 N (c := 1)
    simp only [zero_add] at key
    rw [← key]
  rw [h_range_to_Icc, partial_sum_closed_form N k hk]

-- ═══════════════════════════════════════════════════
-- Truncation error: exact value and bounds
-- ═══════════════════════════════════════════════════

/-- **Exact truncation error.** The difference between the full series value
    `H_k/k` and the partial sum over `range N` equals `(1/k)(H_{N+k} − H_N)`. -/
theorem truncation_error_eq (N k : ℕ) (hk : 0 < k) :
    (∑' n : ℕ, f k n) - ∑ i ∈ Finset.range N, f k i =
      (1 / (k : ℝ)) * ((harmonic (N + k) : ℝ) - (harmonic N : ℝ)) := by
  have htsum : (∑' n : ℕ, f k n) = (harmonic k : ℝ) / (k : ℝ) := by
    unfold f
    exact generalized_triangular_reciprocals_tsum k hk
  rw [htsum, range_partial N k hk]
  ring

/-- **Uniform truncation error bound.** The tail is ≤ `1/(N+1)`, a bound that
    does **not depend on k** — hence holds uniformly over all gaps `k ≥ 1`. -/
theorem truncation_error_le (N k : ℕ) (hk : 0 < k) :
    (∑' n : ℕ, f k n) - ∑ i ∈ Finset.range N, f k i ≤ 1 / ((N : ℝ) + 1) := by
  rw [truncation_error_eq N k hk]
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkinv : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hd := harmonic_diff_le N k
  calc (1 / (k : ℝ)) * ((harmonic (N + k) : ℝ) - (harmonic N : ℝ))
        ≤ (1 / (k : ℝ)) * ((k : ℝ) / ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hd hkinv
    _ = 1 / ((N : ℝ) + 1) := by
          field_simp

/-- **Sharpness.** The tail is ≥ `1/(N+k)`, so the `1/(N+1)` bound cannot be
    improved by more than the factor `(N+1)/(N+k)` (→ 1 as N → ∞ for fixed k). -/
theorem truncation_error_ge (N k : ℕ) (hk : 0 < k) :
    1 / ((N : ℝ) + (k : ℝ)) ≤ (∑' n : ℕ, f k n) - ∑ i ∈ Finset.range N, f k i := by
  rw [truncation_error_eq N k hk]
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkinv : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hd := harmonic_diff_ge N k hk
  calc 1 / ((N : ℝ) + (k : ℝ))
        = (1 / (k : ℝ)) * ((k : ℝ) / ((N : ℝ) + (k : ℝ))) := by field_simp
    _ ≤ (1 / (k : ℝ)) * ((harmonic (N + k) : ℝ) - (harmonic N : ℝ)) :=
          mul_le_mul_of_nonneg_left hd hkinv

/-- **Absolute-value form.** `|S_N − ∑ f| ≤ 1/(N+1)`, uniformly in k. -/
theorem truncation_error_abs (N k : ℕ) (hk : 0 < k) :
    |(∑ i ∈ Finset.range N, f k i) - (∑' n : ℕ, f k n)| ≤ 1 / ((N : ℝ) + 1) := by
  rw [abs_sub_comm]
  have hge : 1 / ((N : ℝ) + (k : ℝ)) ≤
      (∑' n : ℕ, f k n) - ∑ i ∈ Finset.range N, f k i := truncation_error_ge N k hk
  have hnn : (0 : ℝ) ≤ 1 / ((N : ℝ) + (k : ℝ)) := by positivity
  rw [abs_of_nonneg (le_trans hnn hge)]
  exact truncation_error_le N k hk

end TriangularReciprocalsTruncation
