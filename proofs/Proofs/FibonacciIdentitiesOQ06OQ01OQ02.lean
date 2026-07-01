import Mathlib

/-!
# The alternating Fibonacci binomial transform — `∑ (−1)ᵏ C(n,k) F₍ₙ₊d₊ₖ₎ = (−1)ⁿ F_d`

The parent entry `FibonacciIdentitiesOQ06OQ01` proves the **positive** binomial
transform `∑_{k≤n} C(n,k)·Fₘ₊ₖ = F₂ₙ₊ₘ`, where the length-`(n+1)` Fibonacci
window collapses to a single Fibonacci number at the *doubled* index `2n+m`.

This descendant supplies the **alternating** (signed) binomial transform, the
`x = −1` companion of that identity.  Over ℤ,

* `signed_pascal_conv` — the signed analogue of the parent's `pascal_conv`:
  for any `g : ℕ → ℤ`,
  `∑_{k<n+2} (−1)ᵏ C(n+1,k) g(k) = ∑_{k<n+1} (−1)ᵏ C(n,k) g(k)
     − ∑_{k<n+1} (−1)ᵏ C(n,k) g(k+1)`.
  This is the finite-difference identity behind the whole transform: the
  degree-`(n+1)` signed binomial sum equals the *difference* of two degree-`n`
  signed binomial sums at consecutive offsets.

* `fib_alt_binom_transform` — the headline.  For all `n, d`,
  `∑_{k≤n} (−1)ᵏ C(n,k) F₍ₙ₊d₊ₖ₎ = (−1)ⁿ F_d`.
  Applying `signed_pascal_conv` with `g(k) = F₍ₘ₊ₖ₎` turns the recurrence into
  `T(n+1,m) = T(n,m) − T(n,m+1)`, and the Fibonacci recurrence
  `F_{a+1} = F_a + F_{a−1}` collapses `F_{d+1} − F_{d+2} = −F_d`, giving the
  `(−1)ⁿ F_d` closed form with no negative-index Fibonacci.

* `fib_alt_binom_transform_eq` — the same identity in the offset form
  `∑_{k≤n} (−1)ᵏ C(n,k) F₍ₘ₊ₖ₎ = (−1)ⁿ F₍ₘ₋ₙ₎` for `n ≤ m`.

This is the discrete shadow of `1 − φ = ψ` (with `φψ = −1`): applying
`∑ C(n,k)(−1)ᵏ(·)ᵏ` to `φᵐ` sends `φᵐ ↦ φᵐ(1−φ)ⁿ = φᵐψⁿ = (−1)ⁿ φᵐ⁻ⁿ`.

No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ06OQ01OQ02

open Finset

/-- **Signed Pascal convolution over ℤ.**  The degree-`(n+1)` alternating
binomial sum of `g` equals the difference of the two degree-`n` alternating
binomial sums of `g` at offsets `0` and `1`.  This is the signed analogue of the
parent entry's `pascal_conv`. -/
theorem signed_pascal_conv (g : ℕ → ℤ) (n : ℕ) :
    ∑ k ∈ range (n + 2), (-1 : ℤ) ^ k * ((n + 1).choose k : ℤ) * g k
      = (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * g k)
        - ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * g (k + 1) := by
  -- Peel the `k = 0` term off the left sum and reindex the rest by `k ↦ k+1`.
  rw [Finset.sum_range_succ' (fun k => (-1 : ℤ) ^ k * ((n + 1).choose k : ℤ) * g k) (n + 1)]
  -- Pascal's rule `C(n+1,k+1) = C(n,k) + C(n,k+1)` on each reindexed coefficient.
  have hpascal : ∀ k, ((n + 1).choose (k + 1) : ℤ)
      = (n.choose k : ℤ) + (n.choose (k + 1) : ℤ) := by
    intro k; rw [Nat.choose_succ_succ' n k]; push_cast; ring
  -- Split the reindexed sum into the two Pascal pieces.
  have hsplit : (∑ k ∈ range (n + 1),
        (-1 : ℤ) ^ (k + 1) * ((n + 1).choose (k + 1) : ℤ) * g (k + 1))
      = (-(∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * g (k + 1)))
        + (-(∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose (k + 1) : ℤ) * g (k + 1))) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hpascal, pow_succ]
    ring
  rw [hsplit]
  -- The `C(n,k+1)·g(k+1)` sum telescopes against `∑ C(n,k)·g(k)`: reindex it and
  -- match the `k = 0` boundary term `g 0`.
  have htele : (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * g k)
      = (-(∑ k ∈ range n, (-1 : ℤ) ^ k * (n.choose (k + 1) : ℤ) * g (k + 1)))
        + ((-1 : ℤ) ^ 0 * (n.choose 0 : ℤ) * g 0) := by
    rw [Finset.sum_range_succ' (fun k => (-1 : ℤ) ^ k * (n.choose k : ℤ) * g k) n]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  -- The `C(n,k+1)·g(k+1)` sum over `range (n+1)` loses its top term `C(n,n+1)=0`.
  have hdrop : (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose (k + 1) : ℤ) * g (k + 1))
      = ∑ k ∈ range n, (-1 : ℤ) ^ k * (n.choose (k + 1) : ℤ) * g (k + 1) := by
    rw [Finset.sum_range_succ]
    simp [Nat.choose_succ_self]
  rw [hdrop, htele]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one]
  ring

/-- **The alternating Fibonacci binomial transform.**  For all `n, d`,
`∑_{k≤n} (−1)ᵏ C(n,k) F₍ₙ₊d₊ₖ₎ = (−1)ⁿ F_d`.

Proved by induction on `n` with `d` universally quantified.  The step rewrites
the degree-`(n+1)` signed binomial sum via `signed_pascal_conv` into the two
degree-`n` sums at offsets `m = (n+1)+d` and `m+1`, applies the induction
hypothesis to each, and contracts with the Fibonacci recurrence
`F_{d+1} − F_{d+2} = −F_d`. -/
theorem fib_alt_binom_transform (n d : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * (Nat.fib (n + d + k) : ℤ)
      = (-1 : ℤ) ^ n * (Nat.fib d : ℤ) := by
  induction n generalizing d with
  | zero => simp
  | succ p ih =>
    -- Apply the signed convolution with `g k = F₍ₘ₊ₖ₎`, `m = (p+1) + d`.
    have hconv := signed_pascal_conv (fun k => (Nat.fib ((p + 1) + d + k) : ℤ)) p
    -- Rewrite the LHS index `(p+1)+d+k` to match `g` at offset `m = (p+1)+d`.
    have hlhs : (∑ k ∈ range (p + 1 + 1),
          (-1 : ℤ) ^ k * ((p + 1).choose k : ℤ) * (Nat.fib ((p + 1) + d + k) : ℤ))
        = ∑ k ∈ range (p + 2),
          (-1 : ℤ) ^ k * ((p + 1).choose k : ℤ) * (Nat.fib ((p + 1) + d + k) : ℤ) := by
      norm_num
    rw [hlhs, hconv]
    -- First degree-`p` sum: offset `m = (p+1)+d`; its index is `p + (d+1) + k`.
    have hA : (∑ k ∈ range (p + 1),
          (-1 : ℤ) ^ k * (p.choose k : ℤ) * (Nat.fib ((p + 1) + d + k) : ℤ))
        = (-1 : ℤ) ^ p * (Nat.fib (d + 1) : ℤ) := by
      have := ih (d + 1)
      rw [← this]
      apply Finset.sum_congr rfl
      intro k _
      congr 3
      omega
    -- Second degree-`p` sum: offset `m+1`; its index is `p + (d+2) + k`.
    have hB : (∑ k ∈ range (p + 1),
          (-1 : ℤ) ^ k * (p.choose k : ℤ) * (Nat.fib ((p + 1) + d + (k + 1)) : ℤ))
        = (-1 : ℤ) ^ p * (Nat.fib (d + 2) : ℤ) := by
      have := ih (d + 2)
      rw [← this]
      apply Finset.sum_congr rfl
      intro k _
      congr 3
      omega
    rw [hA, hB]
    -- Contract: (−1)ᵖ F_{d+1} − (−1)ᵖ F_{d+2} = (−1)^{p+1} F_d.
    have hfib : (Nat.fib (d + 2) : ℤ) = (Nat.fib d : ℤ) + (Nat.fib (d + 1) : ℤ) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [hfib, pow_succ]
    ring

/-- Offset form: for `n ≤ m`,
`∑_{k≤n} (−1)ᵏ C(n,k) F₍ₘ₊ₖ₎ = (−1)ⁿ F₍ₘ₋ₙ₎`. -/
theorem fib_alt_binom_transform_eq (n m : ℕ) (h : n ≤ m) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * (Nat.fib (m + k) : ℤ)
      = (-1 : ℤ) ^ n * (Nat.fib (m - n) : ℤ) := by
  have key := fib_alt_binom_transform n (m - n)
  have hmn : n + (m - n) = m := by omega
  rw [hmn] at key
  exact key

/-- Headline `d = 0` case: `∑_{k≤n} (−1)ᵏ C(n,k) Fₙ₊ₖ = 0` for `n ≥ 1`
(and `= 1` at `n = 0`), since `F₀ = 0`. -/
theorem fib_alt_binom_transform_zero (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * (Nat.fib (n + k) : ℤ)
      = (-1 : ℤ) ^ n * (Nat.fib 0 : ℤ) := by
  have h := fib_alt_binom_transform n 0
  simpa using h

end FibonacciIdentitiesOQ06OQ01OQ02
