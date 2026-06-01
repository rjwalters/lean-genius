/-
  Generalized Triangular Reciprocals via Harmonic Numbers

  Result: For every integer k ≥ 1,
    ∑_{n=1}^∞ 1/(n(n+k)) = H_k / k

  where H_k = harmonic k = ∑_{i=1}^k 1/i is the k-th harmonic number (Mathlib's
  `harmonic : ℕ → ℚ`, cast to ℝ at the statement boundary).

  Special cases:
    k=1: H_1/1 = 1            (matches the classical Leibniz sum 1/(n(n+1)))
    k=2: H_2/2 = (1 + 1/2)/2 = 3/4
    k=3: H_3/3 = (1 + 1/2 + 1/3)/3 = 11/18

  Proof outline (S3 lock):
    1. partial_fraction:        1/(n(n+k)) = (1/k)(1/n - 1/(n+k))     [lifted from sibling]
    2. partial_sum_closed_form: ∑_{n=1}^N 1/(n(n+k)) = (1/k)(H_k - (H_{N+k} - H_N))
       (reindex the second telescoped term by m = n+k via Finset.sum_Ico_add')
    3. tail_to_zero:            H_{N+k} - H_N → 0 as N → ∞  (since ≤ k/(N+1))
    4. summable_one_div_n_mul_n_add_k:   1/(n(n+k)) ≤ 1/n^2  ⇒  Summable
    Main: combine 2 + 3 + 4 to pass partial sums to HasSum.

  Status: S4 SCAFFOLD — all proofs are `sorry`. ACT phases S5+ will close them.

  Sibling reuse:
    `Proofs/TriangularReciprocalGeneralized.lean` (slug `triangular-reciprocals-oq-03`,
    the *alternating* generalization) provides the `partial_fraction` lemma verbatim.
-/
import Mathlib

namespace TriangularReciprocalsHarmonic

open Finset BigOperators Filter Topology Real

-- ═══════════════════════════════════════════════════
-- Lemma 1: Partial Fraction Decomposition
-- ═══════════════════════════════════════════════════

/-- Partial fraction decomposition: 1/(n(n+k)) = (1/k)(1/n - 1/(n+k)) for k ≠ 0, n ≠ 0.

    Transferred verbatim from `Proofs/TriangularReciprocalGeneralized.lean:133`. -/
theorem partial_fraction {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + ↑k)) =
      (1 / ↑k) * (1 / (n : ℝ) - 1 / ((n : ℝ) + ↑k)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hk' : (↑k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hnk : (n : ℝ) + ↑k ≠ 0 := by positivity
  field_simp
  ring

-- ═══════════════════════════════════════════════════
-- Lemma 2: Closed Form for the Partial Sum
-- ═══════════════════════════════════════════════════

/-- Closed form for the partial sum:

    ∑_{n=1}^{N} 1/(n(n+k)) = (1/k)(H_k - (H_{N+k} - H_N))

    Proof strategy: apply `partial_fraction` to each term, split the sum, reindex the
    second piece by `m = n + k` via `Finset.sum_Ico_add'` (the same lemma used by
    `harmonic_eq_sum_Icc`), and read off the harmonic differences. -/
theorem partial_sum_closed_form (N k : ℕ) (hk : 0 < k) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + ↑k)) =
      (1 / (k : ℝ)) * ((harmonic k : ℝ) - ((harmonic (N + k) : ℝ) - (harmonic N : ℝ))) := by
  sorry

-- ═══════════════════════════════════════════════════
-- Lemma 3: Harmonic Tail Difference Tends to Zero
-- ═══════════════════════════════════════════════════

/-- For fixed k, the harmonic difference H_{N+k} - H_N tends to 0 as N → ∞.

    Proof by induction on k:
      * k = 0: the difference is identically 0.
      * k → k+1: H_{N+(k+1)} - H_N = (H_{N+k} - H_N) + 1/(N+k+1). The first summand
        tends to 0 by the IH; the second is a constant-shift of 1/(N+1), hence → 0
        via `tendsto_one_div_add_atTop_nhds_zero_nat`. -/
theorem tail_to_zero (k : ℕ) :
    Tendsto (fun N : ℕ => (harmonic (N + k) : ℝ) - (harmonic N : ℝ))
      atTop (𝓝 0) := by
  induction k with
  | zero =>
    have hfun : (fun N : ℕ => (harmonic (N + 0) : ℝ) - (harmonic N : ℝ)) =
        fun _ : ℕ => (0 : ℝ) := by
      funext N; simp
    rw [hfun]
    exact tendsto_const_nhds
  | succ k ih =>
    -- Reciprocal-of-shift limit: 1/(N + (k+1)) → 0.
    have h_base : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h_shift : Tendsto (fun N : ℕ => N + k) atTop atTop :=
      tendsto_add_atTop_nat k
    have h_term : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + (k : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) := by
      refine (h_base.comp h_shift).congr ?_
      intro N
      simp only [Function.comp_apply]
      push_cast
      ring
    -- Rewrite the target into the form (H_{N+k} - H_N) + 1/(N+k+1), then sum two zero limits.
    have hgoal :
        (fun N : ℕ => (harmonic (N + (k + 1)) : ℝ) - (harmonic N : ℝ)) =
          fun N : ℕ => ((harmonic (N + k) : ℝ) - (harmonic N : ℝ)) +
            (1 : ℝ) / ((N : ℝ) + (k : ℝ) + 1) := by
      funext N
      have h1 : N + (k + 1) = (N + k) + 1 := rfl
      rw [h1, harmonic_succ]
      push_cast
      ring
    rw [hgoal]
    simpa using ih.add h_term

-- ═══════════════════════════════════════════════════
-- Lemma 4: Summability via p-Series Comparison
-- ═══════════════════════════════════════════════════

/-- The series ∑_{n=1}^∞ 1/(n(n+k)) is summable.

    Proof: term-wise bound 1/(n(n+k)) ≤ 1/n² (since n + k ≥ n ≥ 1 for n ≥ 1), then
    compare with `Real.summable_one_div_nat_pow` at p = 2. -/
theorem summable_one_div_n_mul_n_add_k (k : ℕ) :
    Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + ↑k))) := by
  -- Dominate by the p-series ∑ 1/(n+1)^2, summable via `summable_one_div_nat_pow` at p=2.
  have h_p : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) :=
    summable_one_div_nat_pow.mpr one_lt_two
  have h_shift : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ 2) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) 1).mpr h_p
    simpa using this
  refine Summable.of_nonneg_of_le ?_ ?_ h_shift
  · intro n
    have h1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    positivity
  · intro n
    have h1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hprod : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + (k : ℝ)) := by positivity
    have hsq : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
    rw [div_le_div_iff₀ hprod hsq]
    have : ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by ring
    rw [this]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

-- ═══════════════════════════════════════════════════
-- Main Theorem
-- ═══════════════════════════════════════════════════

/-- **Generalized Triangular Reciprocals via Harmonic Numbers.**

    For every integer k ≥ 1,
      ∑_{n=1}^∞ 1/(n(n+k)) = H_k / k.

    The indexing here is shifted to `n : ℕ` ranging over ℕ, with the running index
    being `n + 1` (avoiding the n = 0 division). This matches the convention used by
    `hasSum_nat_add_iff 1` in the sibling proof. -/
theorem generalized_triangular_reciprocals (k : ℕ) (hk : 0 < k) :
    HasSum (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + ↑k)))
      ((harmonic k : ℝ) / (k : ℝ)) := by
  sorry

/-- tsum version of the main result. -/
theorem generalized_triangular_reciprocals_tsum (k : ℕ) (hk : 0 < k) :
    ∑' n : ℕ, (1 : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + ↑k)) =
      (harmonic k : ℝ) / (k : ℝ) :=
  (generalized_triangular_reciprocals k hk).tsum_eq

-- ═══════════════════════════════════════════════════
-- Verification of Special Cases (k = 1, 2, 3)
-- ═══════════════════════════════════════════════════

/-- k = 1: H_1 / 1 = 1, recovering the classical Leibniz identity. -/
theorem special_case_k1 : ((harmonic 1 : ℝ) / (1 : ℝ)) = 1 := by
  have h : harmonic 1 = 1 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, harmonic_succ, harmonic_zero]
    norm_num
  rw [h]; norm_num

/-- k = 2: H_2 / 2 = 3/4. -/
theorem special_case_k2 : ((harmonic 2 : ℝ) / (2 : ℝ)) = 3 / 4 := by
  have h : harmonic 2 = 3 / 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, harmonic_succ,
        show (1 : ℕ) = 0 + 1 from rfl, harmonic_succ, harmonic_zero]
    norm_num
  rw [h]
  push_cast
  norm_num

/-- k = 3: H_3 / 3 = 11/18. -/
theorem special_case_k3 : ((harmonic 3 : ℝ) / (3 : ℝ)) = 11 / 18 := by
  have h : harmonic 3 = 11 / 6 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, harmonic_succ,
        show (2 : ℕ) = 1 + 1 from rfl, harmonic_succ,
        show (1 : ℕ) = 0 + 1 from rfl, harmonic_succ, harmonic_zero]
    norm_num
  rw [h]
  push_cast
  norm_num

end TriangularReciprocalsHarmonic
