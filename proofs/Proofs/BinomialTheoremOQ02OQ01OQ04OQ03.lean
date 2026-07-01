/-
# All Factorial Moments of the Binomial Marginal (OQ-02-OQ-01-OQ-04-OQ-03)

*Open Question from `BinomialTheoremOQ02OQ01OQ04` (Multinomial Variance).* The
variance file closes the diagonal **second** moment of a multinomial component,
and it does so by reducing to the binomial marginal's first two moments proved
in `BinomialTheoremOQ03`:

  * `binomial_mean`                    : `E[X]      = n·p`      (needs `1 ≤ n`)
  * `binomial_second_factorial_moment` : `E[X(X-1)] = n(n-1)·p²` (needs `2 ≤ n`)

Each was proved separately by peeling off `r` vanishing low-order terms and
applying an `r`-fold "absorption" identity (`absorption`, `double_absorption`).
That approach does not scale: the `r`-th factorial moment would need an
`r`-fold absorption lemma written out by hand.

## Answer

YES — **all** factorial moments have one uniform closed form, with **no** side
condition on `n` or `r`. For `X ~ Binomial(n, p)` and the falling factorial
`(m)_r = m(m-1)⋯(m-r+1) = Nat.descFactorial m r`,

  E[(X)_r] = ∑ₖ (k)_r · C(n,k) pᵏ (1-p)ⁿ⁻ᵏ = (n)_r · pʳ.

Setting `r = 1` recovers `E[X] = n·p` and `r = 2` recovers `E[X(X-1)] =
n(n-1)·p²`, both now valid for *every* `n` (the earlier `1 ≤ n` / `2 ≤ n`
hypotheses were artefacts of the term-peeling proof, not the mathematics).

## Proof Strategy

The engine is the single **subset-of-a-subset** identity for the falling
factorial (one lemma replacing the whole `absorption` tower):

  (k)_r · C(n,k) = (n)_r · C(n-r, k-r)          [for `r ≤ k`]

which follows from Mathlib's `Nat.choose_mul`
(`C(n,k)·C(k,r) = C(n,r)·C(n-r,k-r)`) together with
`descFactorial = r! · choose`. Casting to `ℝ` and matching exponents turns each
term into a *lower* binomial term:

  (k)_r · binomPMF n p k = (n)_r · pʳ · binomPMF (n-r) p (k-r)     [for `r ≤ k ≤ n`].

Summing, the low terms `k < r` vanish (`(k)_r = 0`), the index shifts by `r`,
and what remains is `(n)_r · pʳ` times the normalization
`∑ binomPMF (n-r) p = 1` (`BinomialTheoremOQ03.binomPMF_sum_eq_one`). The case
`r > n` gives `0 = 0` on both sides.

No new axioms, no sorries.

Tags: probability, binomial-distribution, factorial-moment, falling-factorial,
      descFactorial, moments, combinatorics
-/

import Mathlib
import Proofs.BinomialTheoremOQ03

open Finset BigOperators

namespace BinomialTheoremOQ02OQ01OQ04OQ03

open BinomialTheoremOQ03

/-! ## The engine: a single subset-of-a-subset identity -/

/-- **Falling-factorial absorption.** For `r ≤ k`,
`(k)_r · C(n,k) = (n)_r · C(n-r, k-r)`, where `(m)_r = Nat.descFactorial m r`.

This one identity subsumes the entire `absorption` / `double_absorption` tower
used for the first and second factorial moments: it is the `r`-fold statement.
It is `Nat.choose_mul` (`C(n,k)·C(k,r) = C(n,r)·C(n-r,k-r)`) dressed with
`descFactorial = r! · choose`. -/
theorem descFactorial_mul_choose (n k r : ℕ) (hrk : r ≤ k) :
    k.descFactorial r * n.choose k = n.descFactorial r * (n - r).choose (k - r) := by
  have hcm := Nat.choose_mul (n := n) (k := k) (s := r) hrk
  -- hcm : n.choose k * k.choose r = n.choose r * (n - r).choose (k - r)
  rw [Nat.descFactorial_eq_factorial_mul_choose k r,
      Nat.descFactorial_eq_factorial_mul_choose n r, mul_assoc, mul_assoc]
  -- goal: r! * (C(k,r) * C(n,k)) = r! * (C(n,r) * C(n-r,k-r))
  congr 1
  rw [mul_comm]
  exact hcm

/-- **Termwise reduction.** For `r ≤ k ≤ n`, a single falling-factorial-weighted
binomial term collapses to `(n)_r · pʳ` times a *lower* binomial PMF:

  `(k)_r · binomPMF n p k = (n)_r · pʳ · binomPMF (n-r) p (k-r)`. -/
private theorem descFactorial_mul_binomPMF (n r k : ℕ) (p : ℝ)
    (hrk : r ≤ k) (hkn : k ≤ n) :
    (k.descFactorial r : ℝ) * binomPMF n p k =
    (n.descFactorial r : ℝ) * p ^ r * binomPMF (n - r) p (k - r) := by
  unfold binomPMF
  have hnat : (k.descFactorial r : ℝ) * (n.choose k : ℝ) =
      (n.descFactorial r : ℝ) * ((n - r).choose (k - r) : ℝ) := by
    exact_mod_cast descFactorial_mul_choose n k r hrk
  have hp : p ^ k = p ^ r * p ^ (k - r) := by rw [← pow_add]; congr 1; omega
  have hq : (1 - p) ^ (n - k) = (1 - p) ^ (n - r - (k - r)) := by congr 1; omega
  calc (k.descFactorial r : ℝ) * ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
      = ((k.descFactorial r : ℝ) * (n.choose k : ℝ)) * p ^ k * (1 - p) ^ (n - k) := by ring
    _ = ((n.descFactorial r : ℝ) * ((n - r).choose (k - r) : ℝ)) * p ^ k *
          (1 - p) ^ (n - k) := by rw [hnat]
    _ = (n.descFactorial r : ℝ) * p ^ r *
          (((n - r).choose (k - r) : ℝ) * p ^ (k - r) * (1 - p) ^ (n - r - (k - r))) := by
          rw [hp, hq]; ring

/-! ## The general factorial moment -/

/-- **General factorial moment of the binomial distribution.**
For every `n, r : ℕ` and every `p : ℝ`,

  `E[(X)_r] = ∑ₖ (k)_r · binomPMF n p k = (n)_r · pʳ`,

where `(m)_r = Nat.descFactorial m r = m(m-1)⋯(m-r+1)` is the falling factorial.
No lower bound on `n` or `r` is required. -/
theorem binomial_factorial_moment (n r : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1), (k.descFactorial r : ℝ) * binomPMF n p k =
    (n.descFactorial r : ℝ) * p ^ r := by
  rcases le_or_gt r n with hrn | hrn
  · -- `r ≤ n`: shift the index and reduce to lower-order normalization.
    -- Terms with `k < r` vanish, so restrict the sum to `Ico r (n+1)`.
    have hsplit : ∑ k ∈ range (n + 1), (k.descFactorial r : ℝ) * binomPMF n p k =
        ∑ k ∈ Ico r (n + 1), (k.descFactorial r : ℝ) * binomPMF n p k := by
      rw [Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le r) (by omega : r ≤ n + 1)]
      have hzero : ∑ k ∈ Ico 0 r, (k.descFactorial r : ℝ) * binomPMF n p k = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_Ico] at hk
        have : k.descFactorial r = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hk.2
        rw [this]; simp
      rw [hzero, zero_add]
    rw [hsplit, Finset.sum_Ico_eq_sum_range]
    -- Now `∑ i ∈ range (n+1-r), (r+i)_r · binomPMF n p (r+i)`.
    have hterms : ∀ i ∈ range (n + 1 - r),
        ((r + i).descFactorial r : ℝ) * binomPMF n p (r + i) =
        (n.descFactorial r : ℝ) * p ^ r * binomPMF (n - r) p i := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hkn : r + i ≤ n := by omega
      have hstep := descFactorial_mul_binomPMF n r (r + i) p (Nat.le_add_right r i) hkn
      have hri : r + i - r = i := by omega
      rw [hri] at hstep
      exact hstep
    rw [Finset.sum_congr rfl hterms, ← Finset.mul_sum]
    have hone : ∑ i ∈ range (n + 1 - r), binomPMF (n - r) p i = 1 := by
      rw [show n + 1 - r = (n - r) + 1 by omega]
      exact binomPMF_sum_eq_one (n - r) p
    rw [hone, mul_one]
  · -- `r > n`: both sides are `0`.
    have hdn : n.descFactorial r = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hrn
    rw [hdn]
    simp only [Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    have : k.descFactorial r = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [this]; simp

/-! ## Recovering the mean and the second factorial moment

Both special cases of `binomial_factorial_moment` now hold for **every** `n`,
dropping the `1 ≤ n` and `2 ≤ n` hypotheses of the original term-peeling proofs
in `BinomialTheoremOQ03`. -/

/-- The zeroth factorial moment is normalization: `E[1] = 1`. (`r = 0`.) -/
theorem binomial_zeroth_factorial_moment (n : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1), binomPMF n p k = 1 := by
  have h := binomial_factorial_moment n 0 p
  simpa using h

/-- `r = 1`: the mean `E[X] = n·p`, now with **no** lower bound on `n`
(cf. `BinomialTheoremOQ03.binomial_mean`, which requires `1 ≤ n`). -/
theorem binomial_mean' (n : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1), (k : ℝ) * binomPMF n p k = (n : ℝ) * p := by
  have h := binomial_factorial_moment n 1 p
  simpa [Nat.descFactorial_one, pow_one] using h

/-- `r = 2`: the second factorial moment `E[X(X-1)] = n(n-1)·p²`, now with **no**
lower bound on `n` (cf. `BinomialTheoremOQ03.binomial_second_factorial_moment`,
which requires `2 ≤ n`). -/
theorem binomial_second_factorial_moment' (n : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1), ((k : ℝ) * ((k : ℝ) - 1)) * binomPMF n p k =
    (n : ℝ) * ((n : ℝ) - 1) * p ^ 2 := by
  have h := binomial_factorial_moment n 2 p
  simp only [Nat.cast_descFactorial_two] at h
  convert h using 2

/-- `r = 3`: the third factorial moment `E[X(X-1)(X-2)] = n(n-1)(n-2)·p³` — a
genuinely new closed form beyond what the previous absorption tower reached. -/
theorem binomial_third_factorial_moment (n : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1),
        ((k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2)) * binomPMF n p k =
    (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * p ^ 3 := by
  have h := binomial_factorial_moment n 3 p
  have hcast : ∀ m : ℕ, (m.descFactorial 3 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) := by
    intro m
    match m with
    | 0 => simp
    | 1 => simp [Nat.descFactorial]
    | 2 => simp [Nat.descFactorial]
    | (k + 3) =>
        have hnat : (k + 3).descFactorial 3 = (k + 3) * (k + 2) * (k + 1) := by
          rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial,
              Nat.descFactorial_zero, mul_one]
          rw [show k + 3 - 0 = k + 3 from rfl, show k + 3 - 1 = k + 2 from by omega,
              show k + 3 - 2 = k + 1 from by omega]
          ring
        rw [hnat]; push_cast; ring
  simp only [hcast] at h
  convert h using 2

end BinomialTheoremOQ02OQ01OQ04OQ03
