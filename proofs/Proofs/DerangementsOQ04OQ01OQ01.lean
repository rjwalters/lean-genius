import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast

/-!
# Poisson(1) limit of the fixed-point distribution of a random permutation

Let `σ` be a permutation of an `n`-element set chosen uniformly at random, and let
`X_n = #{fixed points of σ}`. A classical result (going back to Montmort's *problème
des rencontres*) is that the distribution of `X_n` converges, as `n → ∞`, to a
**Poisson distribution with mean `1`**:
`P(X_n = k) → e⁻¹ / k!` for each fixed `k`.

## The exact finite distribution

The number of permutations of `[n]` with *exactly* `k` fixed points is
`C(n, k) · D(n − k)`, where `D = numDerangements` counts the derangements (choose
which `k` points are fixed, then derange the remaining `n − k`). Hence
`P(X_n = k) = C(n, k) · D(n − k) / n!`.
These probabilities sum to one: `∑_{k=0}^{n} C(n, k) · D(n − k) = n!` (the
derangement convolution identity, formalized in the sibling
`derangements-convergence` entries).

## What is proved here (all `0`-axiom, no `sorry`)

* `fixedPointProb n k` — the exact finite probability `C(n, k) · D(n − k) / n!`.
* `fixedPointProb_eq` — for `k ≤ n`, `fixedPointProb n k = (D(n−k) / (n−k)!) / k!`,
  peeling the binomial coefficient into a derangement density times `1 / k!`.
* `fixedPointProb_tendsto` — **the Poisson(1) limit**: for each fixed `k`,
  `fixedPointProb n k → e⁻¹ / k!` as `n → ∞`. This is the analytic heart of the
  theorem; it reduces the whole statement to Mathlib's
  `numDerangements_tendsto_inv_e` (`D(n)/n! → e⁻¹`) via the reindexing `n ↦ n − k`
  and multiplication by the constant `1 / k!`.

## Remaining gap (the combinatorial count)

Mathlib does not (yet) contain the exact-count identity
`#{σ : Perm (Fin n) // #fixedPoints σ = k} = C(n, k) · D(n − k)`; establishing it
requires an explicit equivalence
`{σ // #fixedPoints σ = k} ≃ Σ (s : {s : Finset (Fin n) // s.card = k}), derangements ↥sᶜ`.
That combinatorial identity is the natural next brick; once it is in place, the
limit proved here upgrades from a statement about the *formula* `C(n,k)·D(n−k)/n!`
to a statement about the genuine *probability* `P(X_n = k)` with no further analysis.
-/

open Filter Topology
open scoped Nat

namespace DerangementsOQ04OQ01OQ01

/-- The exact probability that a uniform random permutation of `[n]` has exactly
`k` fixed points: `C(n, k) · D(n − k) / n!` (with `D = numDerangements`). -/
noncomputable def fixedPointProb (n k : ℕ) : ℝ :=
  (n.choose k * numDerangements (n - k) : ℝ) / n.factorial

/-- For `k ≤ n`, the fixed-point probability factors as a **derangement density**
`D(n−k) / (n−k)!` times `1 / k!`. This is the identity that turns the Poisson
limit into a one-line consequence of `numDerangements_tendsto_inv_e`. -/
theorem fixedPointProb_eq {n k : ℕ} (hn : k ≤ n) :
    fixedPointProb n k
      = (numDerangements (n - k) : ℝ) / (n - k).factorial * (1 / k.factorial) := by
  unfold fixedPointProb
  rw [Nat.cast_choose (K := ℝ) hn]
  have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hnk : ((n - k).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Poisson(1) limit of the fixed-point distribution.**
For each fixed number `k` of fixed points, the exact finite probability converges
to the Poisson(1) mass `e⁻¹ / k!`:
`C(n, k) · D(n − k) / n! → e⁻¹ / k!` as `n → ∞`. -/
theorem fixedPointProb_tendsto (k : ℕ) :
    Tendsto (fun n => fixedPointProb n k) atTop (𝓝 (Real.exp (-1) / k.factorial)) := by
  -- reindex Mathlib's `D(n)/n! → e⁻¹` along `n ↦ n − k`
  have hbase : Tendsto (fun n => (numDerangements (n - k) : ℝ) / (n - k).factorial)
      atTop (𝓝 (Real.exp (-1))) :=
    numDerangements_tendsto_inv_e.comp (tendsto_sub_atTop_nat k)
  -- multiply by the constant `1 / k!`
  have hmul := hbase.mul_const (1 / k.factorial : ℝ)
  rw [mul_one_div] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [fixedPointProb_eq hn]

/-- Spelled-out form of the limit directly in terms of the counting formula. -/
theorem choose_mul_numDerangements_div_factorial_tendsto (k : ℕ) :
    Tendsto (fun n => (n.choose k * numDerangements (n - k) : ℝ) / n.factorial)
      atTop (𝓝 (Real.exp (-1) / k.factorial)) :=
  fixedPointProb_tendsto k

/-- The `k = 0` case recovers the derangement probability `D(n)/n! → e⁻¹`
(the probability of *no* fixed points). -/
theorem fixedPointProb_zero_tendsto :
    Tendsto (fun n => fixedPointProb n 0) atTop (𝓝 (Real.exp (-1))) := by
  have h := fixedPointProb_tendsto 0
  simpa using h

end DerangementsOQ04OQ01OQ01
