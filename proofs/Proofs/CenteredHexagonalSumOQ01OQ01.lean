/-
# Centered Polygonal Partial Sums — a Uniform Closed Form

## Open question (`centered-hexagonal-sum-oq-01-oq-01`)

The parent entry `centered-hexagonal-sum-oq-01` proves the figurate identity that the
first `n` *centered hexagonal* numbers sum to the perfect cube `n³`. Its open question
asks whether the analogous **centered `k`-gonal** partial sums admit equally clean closed
forms, and which reindexing keeps each computation inside the naturals.

## Result

For every `k`, the `n`-th centered `k`-gonal number is `C_{k,n} = k·n(n−1)/2 + 1`
(the centre dot plus `k` triangular arms); `k = 6` is the centered hexagonal case
`3n(n−1)+1`. The partial sums obey a single **uniform closed form**, valid for all `k`
simultaneously and stated without any division or truncated subtraction:

    6 · ∑_{i=1}^{n} C_{k,i}  =  k·n³ + (6−k)·n.

* `six_mul_cgon_succ` — the per-term `/2` is eliminated once and for all: `n(n+1)` is
  always even, so `6·C_{k,n+1} = 3·(k·n(n+1)) + 6` is a genuine ℕ identity.
* `six_mul_sum_cgon` — the headline closed form `6·∑ C_{k,i} = k·n³ + (6−k)·n`, over ℤ
  so the single coefficient `6−k` carries every centered-polygonal family at once
  (k=3 centered triangular, k=4 centered square, k=5 centered pentagonal, …).
* `cgon_six` / `sum_centeredHex_cube` — specialising to `k = 6` collapses `6−k` to `0`,
  recovering the parent's cube identity `∑ C_{6,i} = n³` as a one-line corollary.

The reindexing answer to the open question: scale by the denominator `6` and move the
linear part to the other side (`+ (6−k)·n` rather than `− (k−6)·n`); then no division and
no ℕ-subtraction ever appear, and `k = 6` is the unique value making the partial sums a
pure power.

0 sorries, 0 axioms.
-/

import Mathlib

namespace CenteredHexagonalSumOQ01OQ01

open Finset

/-- The `n`-th **centered `k`-gonal number** `C_{k,n} = k·n(n−1)/2 + 1`: a central dot
plus `k` triangular arms of `n−1` rings. `k = 6` gives the centered hexagonal numbers
`3n(n−1)+1` of the parent entry; `k = 3, 4, 5` give the centered triangular, square, and
pentagonal numbers. -/
def cgon (k n : ℕ) : ℕ := k * (n * (n - 1)) / 2 + 1

/-- For `k = 6` the definition is the parent entry's centered hexagonal number
`C_{6,n} = 3·n(n−1) + 1`. -/
theorem cgon_six (n : ℕ) : cgon 6 n = 3 * (n * (n - 1)) + 1 := by
  unfold cgon
  omega

/-- **Eliminating the `/2`.** Because `n(n+1)` is always even, the reindexed term has the
honest ℕ identity `6·C_{k,n+1} = 3·(k·n(n+1)) + 6` — no division survives. -/
theorem six_mul_cgon_succ (k n : ℕ) :
    6 * cgon k (n + 1) = 3 * (k * (n * (n + 1))) + 6 := by
  have hdvd : 2 ∣ k * (n * (n + 1)) :=
    (even_iff_two_dvd.mp (Nat.even_mul_succ_self n)).mul_left k
  have hcgon : cgon k (n + 1) = k * (n * (n + 1)) / 2 + 1 := by
    unfold cgon
    rw [Nat.add_sub_cancel, Nat.mul_comm (n + 1) n]
  rw [hcgon]
  omega

/-- **Uniform closed form for centered-polygonal partial sums.** Over ℤ, for every `k`,

`6 · ∑_{i<n} C_{k,i+1} = k·n³ + (6−k)·n`,

a single formula carrying every centered `k`-gonal family. The reindexed sum `∑_{i<n}
C_{k,i+1}` is the `1`-indexed sum `∑_{i=1}^{n} C_{k,i}`. -/
theorem six_mul_sum_cgon (k n : ℕ) :
    6 * (∑ i ∈ range n, (cgon k (i + 1) : ℤ))
      = (k : ℤ) * (n : ℤ) ^ 3 + (6 - (k : ℤ)) * (n : ℤ) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, mul_add, ih]
      have hC : (6 : ℤ) * (cgon k (m + 1) : ℤ) = 3 * ((k : ℤ) * ((m : ℤ) * (m + 1))) + 6 := by
        exact_mod_cast six_mul_cgon_succ k m
      rw [hC]
      push_cast
      ring

/-- **Parent identity as a corollary** (`k = 6`). Centered hexagonal partial sums are
cubes: `∑_{i=1}^{n} C_{6,i} = n³`. Specialising the uniform closed form to `k = 6` makes
the linear coefficient `6 − k` vanish, leaving `6·∑ = 6·n³`. -/
theorem sum_centeredHex_cube (n : ℕ) :
    ∑ i ∈ range n, cgon 6 (i + 1) = n ^ 3 := by
  have h := six_mul_sum_cgon 6 n
  have h6 : (6 : ℤ) * (∑ i ∈ range n, (cgon 6 (i + 1) : ℤ)) = 6 * (n : ℤ) ^ 3 := by
    rw [h]; ring
  have hz : (∑ i ∈ range n, (cgon 6 (i + 1) : ℤ)) = (n : ℤ) ^ 3 := by linarith
  exact_mod_cast hz

end CenteredHexagonalSumOQ01OQ01
