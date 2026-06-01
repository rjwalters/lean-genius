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
  sorry

/-- Lemma 3 (companion form): the harmonic tail difference tends to 0.

    For fixed k, H_{N+k} - H_N → 0 as N → ∞. Aristotle target: combine the
    quantitative bound H_{N+k} - H_N ≤ k/(N+1) with `tendsto_const_div_atTop_nhds_zero_nat`. -/
theorem tail_to_zero_aristotle (k : ℕ) :
    Tendsto (fun N : ℕ => (harmonic (N + k) : ℝ) - (harmonic N : ℝ))
      atTop (𝓝 0) := by
  sorry

/-- Lemma 4 (companion form): the series ∑ 1/((n+1)((n+1)+k)) is summable.

    Aristotle target: p-series comparison with 1/(n+1)^2 via
    `Real.summable_one_div_nat_pow` at p = 2. -/
theorem summable_one_div_n_mul_n_add_k_aristotle (k : ℕ) :
    Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + ↑k))) := by
  sorry

end TriangularReciprocalsHarmonic.Aristotle
