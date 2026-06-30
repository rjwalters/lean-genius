/-
  The Poisson(1) Limiting Distribution of Fixed Points
  (derangements-oq-02-oq-01-oq-01)

  Source: open question of derangements-oq-02-oq-01.

  The parent entry `DerangementsOQ02OQ01` proves the exact partial-derangement
  count for an arbitrary finite type:

    `card_perms_with_kfixed_fintype`:
      |{σ : Perm α | |Fix σ| = k}| = C(|α|, k) · D(|α| − k)

  where `D = numDerangements` is the derangement sequence.  This file extracts
  the *asymptotic* content of that count.  Writing `Sₙ` for the symmetric group
  on `n` letters and

    `prob n k := |{σ ∈ Sₙ | |Fix σ| = k}| / n!`

  for the probability that a uniformly random permutation of `n` letters fixes
  exactly `k` points, the parent count and the elementary identity
  `n! = C(n,k)·k!·(n−k)!` collapse the ratio to

    **`kfixed_prob_eq`** :  `prob n k = (1/k!) · (D(n−k)/(n−k)!)`   (for `k ≤ n`).

  Mathlib records the classical derangement limit
  `numDerangements_tendsto_inv_e : D(m)/m! → e⁻¹`.  Composing it with `m = n−k`
  (which tends to `∞` for fixed `k`) gives the headline result:

    **`kfixed_prob_tendsto`** :  `prob n k → e⁻¹ / k!`   as `n → ∞`.

  This is the **Poisson(1) limiting distribution**: the number of fixed points of
  a random permutation converges in distribution to a Poisson random variable of
  mean `1`, whose point masses are `e⁻¹/k!`.  We also record that for every `n`
  the `prob n ·` are genuine probabilities (`kfixed_prob_sum`: they sum to `1`),
  matching the total mass `∑ₖ e⁻¹/k! = e⁻¹·e = 1` of the limit.

  ## Relation to Mathlib

  Mathlib has the derangement count, the recursion, and the scalar limit
  `D(m)/m! → e⁻¹`, but it does not state the distribution of the number of fixed
  points of a random permutation.  We assemble that limiting distribution from
  the parent's exact partial-derangement count and the Mathlib scalar limit.
-/

import Mathlib
import Proofs.DerangementsOQ02OQ01

open Filter Topology Finset
open scoped Nat

namespace DerangementsOQ02OQ01OQ01

/-- Number of permutations of `Fin n` with exactly `k` fixed points. -/
def kFixedCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (Finset.univ.filter (fun x => σ x = x)).card = k)).card

/-- **Exact count, specialised to `Fin n`.**  `kFixedCount n k = C(n,k)·D(n−k)`,
the parent partial-derangement formula evaluated on `Fin n`. -/
theorem kFixedCount_eq (n k : ℕ) (hk : k ≤ n) :
    kFixedCount n k = n.choose k * numDerangements (n - k) := by
  have h := PartialDerangementsGeneral.card_perms_with_kfixed_fintype
    (α := Fin n) k (by simpa using hk)
  simpa [kFixedCount, Fintype.card_fin] using h

/-- Probability that a uniformly random permutation of `Fin n` fixes exactly
`k` points. -/
noncomputable def prob (n k : ℕ) : ℝ := (kFixedCount n k : ℝ) / n.factorial

/-- **The probability collapses to `(1/k!)·(D(n−k)/(n−k)!)`** for `k ≤ n`.
This is the bridge between the exact count and the derangement limit: the
binomial coefficient cancels against `n! = C(n,k)·k!·(n−k)!`. -/
theorem kfixed_prob_eq (n k : ℕ) (hk : k ≤ n) :
    prob n k = (1 / (k.factorial : ℝ)) * ((numDerangements (n - k) : ℝ) / (n - k).factorial) := by
  have hfact : (n ! : ℝ) = (n.choose k : ℝ) * k.factorial * (n - k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial hk
    exact_mod_cast this.symm
  have hck : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hkf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hnkf : (0 : ℝ) < ((n - k).factorial : ℝ) := by exact_mod_cast (n - k).factorial_pos
  rw [prob, kFixedCount_eq n k hk]
  push_cast
  rw [hfact]
  field_simp

/-- For every `n`, the numbers `prob n k` are a genuine probability distribution:
they sum to `1` over `0 ≤ k ≤ n`. -/
theorem kfixed_prob_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), prob n k = 1 := by
  have hn : (n ! : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hsum := PartialDerangementsGeneral.sum_kfixed_eq_factorial (α := Fin n)
  rw [Fintype.card_fin] at hsum
  have hnatsum : ∑ k ∈ Finset.range (n + 1), kFixedCount n k = n ! := hsum
  have hcast : ∑ k ∈ Finset.range (n + 1), (kFixedCount n k : ℝ) = (n ! : ℝ) := by
    exact_mod_cast hnatsum
  calc ∑ k ∈ Finset.range (n + 1), prob n k
      = (∑ k ∈ Finset.range (n + 1), (kFixedCount n k : ℝ)) / n.factorial := by
        rw [Finset.sum_div]; rfl
    _ = (n ! : ℝ) / n.factorial := by rw [hcast]
    _ = 1 := by rw [div_self hn]

/-- **Poisson(1) limiting distribution.**  For a fixed number of fixed points
`k`, the probability that a uniformly random permutation of `n` letters fixes
exactly `k` points converges to `e⁻¹/k!` as `n → ∞`:

  `prob n k → e⁻¹ / k!`.

The number of fixed points of a random permutation thus converges in
distribution to a Poisson(1) random variable. -/
theorem kfixed_prob_tendsto (k : ℕ) :
    Tendsto (fun n => prob n k) atTop (𝓝 (Real.exp (-1) / k.factorial)) := by
  -- `n ↦ n - k` runs to infinity (for fixed `k`).
  have hsub : Tendsto (fun n : ℕ => n - k) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b + k, fun n hn => by omega⟩)
  -- so `D(n−k)/(n−k)! → e⁻¹` by Mathlib's derangement limit.
  have hgk : Tendsto (fun n : ℕ => (numDerangements (n - k) : ℝ) / (n - k).factorial)
      atTop (𝓝 (Real.exp (-1))) :=
    numDerangements_tendsto_inv_e.comp hsub
  -- scale by the constant `1/k!`.
  have hlim : Tendsto
      (fun n : ℕ => (1 / (k.factorial : ℝ)) *
        ((numDerangements (n - k) : ℝ) / (n - k).factorial))
      atTop (𝓝 (Real.exp (-1) / k.factorial)) := by
    have h := hgk.const_mul (1 / (k.factorial : ℝ))
    rwa [show (1 / (k.factorial : ℝ)) * Real.exp (-1) = Real.exp (-1) / k.factorial by ring] at h
  -- `prob n k` agrees with the scaled limit eventually (once `k ≤ n`).
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (kfixed_prob_eq n k hn).symm

end DerangementsOQ02OQ01OQ01
