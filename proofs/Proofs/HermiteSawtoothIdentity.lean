/-
# Companion Sawtooth Identity for Hermite's Identity

For every real `x` and every integer `n ≥ 1`,
$$\sum_{k=0}^{n-1} \left\{ x + \frac{k}{n} \right\} = \{n x\} + \frac{n-1}{2},$$
where `{y} = y - ⌊y⌋` is the fractional part (`Int.fract`).

This is the fractional-part twin of Hermite's floor identity
`∑_{k=0}^{n-1} ⌊x + k/n⌋ = ⌊n x⌋` (the parent gallery entry
`HermiteFloorIdentity.lean`).  The two are two faces of one fact: summing the
real numbers `x + k/n` over `k = 0, …, n-1` gives the exact value
`n x + (n-1)/2`, which splits as

* the **floor** side `⌊n x⌋` (Hermite's identity), plus
* the **sawtooth** side `{n x} + (n-1)/2`.

## Strategy

Entirely elementary; the parent identity does the analytic work.

1. **Exact arithmetic sum.** `∑_{k=0}^{n-1} (x + k/n) = n x + (n-1)/2`, using
   `∑_{k<n} x = n x` and the Gauss sum `∑_{k<n} k = n(n-1)/2`.
2. **Split fractional parts.** Each `{y} = y - ⌊y⌋`, so
   `∑ {x+k/n} = (∑ (x+k/n)) - (∑ ⌊x+k/n⌋)`.
3. **Apply Hermite.** The floor sum is `⌊n x⌋` (parent theorem), leaving
   `n x + (n-1)/2 - ⌊n x⌋ = {n x} + (n-1)/2`.

No axioms beyond Lean/Mathlib's foundations; `0` sorries.
-/
import Mathlib
import Proofs.HermiteFloorIdentity

open Finset

namespace HermiteSawtoothIdentity

/-- **Exact sampled sum.**  For `n ≥ 1` and any real `x`, the equally spaced
samples `x + k/n` for `k = 0, …, n-1` sum to `n x + (n-1)/2`. -/
theorem sum_sample (x : ℝ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, (x + (k : ℝ) / (n : ℝ)) = (n : ℝ) * x + ((n : ℝ) - 1) / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- Gauss sum over ℝ: `∑_{k<n} k = n(n-1)/2`.
  have hgauss : ∑ k ∈ range n, (k : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    have h := Finset.sum_range_id_mul_two n
    have hc := congrArg (fun m : ℕ => (m : ℝ)) h
    push_cast [Nat.cast_sub hn] at hc
    -- hc : (∑ i ∈ range n, ↑i) * 2 = ↑n * (↑n - 1)
    linear_combination hc / 2
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [show (∑ k ∈ range n, (k : ℝ) / (n : ℝ)) = (∑ k ∈ range n, (k : ℝ)) / (n : ℝ) by
    rw [Finset.sum_div]]
  rw [hgauss]
  field_simp

/-- **Companion sawtooth identity.**  For every real `x` and every `n ≥ 1`,
`∑_{k=0}^{n-1} {x + k/n} = {n x} + (n-1)/2`, where `{·} = Int.fract`. -/
theorem hermite_sawtooth_identity (x : ℝ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, Int.fract (x + (k : ℝ) / (n : ℝ))
      = Int.fract ((n : ℝ) * x) + ((n : ℝ) - 1) / 2 := by
  -- Split each fractional part `{y} = y - ⌊y⌋`.
  have hfract : ∀ k ∈ range n,
      Int.fract (x + (k : ℝ) / (n : ℝ))
        = (x + (k : ℝ) / (n : ℝ)) - (⌊x + (k : ℝ) / (n : ℝ)⌋ : ℝ) := by
    intro k _; rw [Int.fract]
  rw [Finset.sum_congr rfl hfract, Finset.sum_sub_distrib]
  -- Floor sum collapses to `⌊n x⌋` by Hermite's identity.
  rw [← Int.cast_sum, HermiteFloorIdentity.hermite_floor_identity x n hn]
  -- Exact sampled sum on the remaining term.
  rw [sum_sample x n hn]
  -- `{n x} = n x - ⌊n x⌋`.
  rw [Int.fract]
  ring

/-- **Floor + sawtooth decomposition.**  The exact sampled sum splits as the
Hermite floor side plus the sawtooth side, making the floor↔fractional
equivalence explicit. -/
theorem floor_add_sawtooth (x : ℝ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range n, (x + (k : ℝ) / (n : ℝ))
      = ((⌊(n : ℝ) * x⌋ : ℝ))
        + (∑ k ∈ range n, Int.fract (x + (k : ℝ) / (n : ℝ))) := by
  rw [hermite_sawtooth_identity x n hn, sum_sample x n hn, Int.fract]
  ring

end HermiteSawtoothIdentity
