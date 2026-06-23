/-
  Aristotle companion for `TriangularReciprocalsOQ02.lean`.

  Exposes only the *transferable / mechanizable* supporting lemmas (1, 3, 4) as
  theorem sorries, in shapes Aristotle is likely to close. Lemma 2
  (`partial_sum_closed_form`) carries the substantive reindexing argument and is
  kept inside the main file per gallery convention.

  See `research/SORRY-CLASSIFICATION.md` for the companion-file template and rules
  (definitions complete, no axioms, no `True` placeholders, etc.).
-/
import Mathlib

namespace TriangularReciprocalsHarmonic.Aristotle

open Finset BigOperators Filter Topology Real

/-- Lemma 1 (companion form): partial fraction decomposition.

    1/(n(n+k)) = (1/k)(1/n - 1/(n+k))  for k ≠ 0, n ≠ 0.

    Direct from `field_simp; ring` after the `Nat.cast_ne_zero` hypotheses. -/
theorem partial_fraction_aristotle {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + ↑k)) =
      (1 / ↑k) * (1 / (n : ℝ) - 1 / ((n : ℝ) + ↑k)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hk' : (↑k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hnk : (n : ℝ) + ↑k ≠ 0 := by positivity
  field_simp
  ring

/-- Lemma 3 (companion form): the harmonic tail difference tends to 0.

    For fixed k, H_{N+k} - H_N → 0 as N → ∞. Proof by induction on k, using
    `tendsto_one_div_add_atTop_nhds_zero_nat` for the per-term limit
    1/(N+k+1) → 0 in the successor step. -/
theorem tail_to_zero_aristotle (k : ℕ) :
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

/-- Lemma 4 (companion form): the series ∑ 1/((n+1)((n+1)+k)) is summable.

    Aristotle target: p-series comparison with 1/(n+1)^2 via
    `Real.summable_one_div_nat_pow` at p = 2. -/
theorem summable_one_div_n_mul_n_add_k_aristotle (k : ℕ) :
    Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + ↑k))) := by
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

end TriangularReciprocalsHarmonic.Aristotle
