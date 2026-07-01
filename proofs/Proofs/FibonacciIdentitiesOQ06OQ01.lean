import Mathlib

/-!
# The Fibonacci binomial transform — `∑ C(n,k)·Fₘ₊ₖ = F₂ₙ₊ₘ`

The parent entry `FibonacciIdentitiesOQ06` records the two elementary *linear*
Fibonacci summation identities: the partial sum `∑ Fᵢ = Fₙ₊₂ − 1` and the
index-weighted first moment `∑ i·Fᵢ`. Every summand there depends on the running
index only through a *fixed* Fibonacci value or a polynomial coefficient. This
open-question descendant supplies the qualitatively different **binomial
transform**, in which the summation weights are the binomial coefficients
`C(n,k)` — a nonlinear, self-referential weighting that folds the sequence back
onto itself at a *doubled* index:

* `fib_binom_transform` — for all `n, m`,
  `∑_{k≤n} C(n,k)·Fₘ₊ₖ = F₂ₙ₊ₘ`.
  The binomial-weighted sum of a length-`(n+1)` Fibonacci window starting at `m`
  collapses to a single Fibonacci number whose index is `2n + m`. The `m`
  parameter is essential: it is what makes the induction close (the step needs
  the identity at both `m` and `m+1`).

* `fib_binom_transform_zero` — the headline case `m = 0`:
  `∑_{k≤n} C(n,k)·Fₖ = F₂ₙ`.
  The binomial transform of the Fibonacci sequence is the Fibonacci sequence
  read at even indices. This is the discrete shadow of the golden-ratio identity
  `1 + φ = φ²`: applying `∑ C(n,k)(·)ᵏ` to `φ` sends `φ ↦ (1+φ)ⁿ = φ²ⁿ`.

The engine is a general **Pascal convolution** for any `ℕ`-valued summand,
`pascal_conv`, proved from Pascal's rule `C(n+1,k+1) = C(n,k) + C(n,k+1)` and the
two range-peeling lemmas (`Finset.sum_range_succ'`, `Finset.sum_range_succ`)
together with the vanishing `C(n,n+1) = 0`. It splits a length-`(n+2)` binomial
sum for `n+1` into the two length-`(n+1)` binomial sums for `n` at consecutive
offsets — exactly the shape the Fibonacci recurrence `Fₐ + Fₐ₊₁ = Fₐ₊₂` then
contracts.

No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ06OQ01

open Finset

/-- **Pascal convolution.** For any summand `f : ℕ → ℕ`, the binomial-weighted
sum with `C(n+1, ·)` over a length-`(n+2)` window equals the sum of the two
`C(n, ·)`-weighted length-`(n+1)` windows at offsets `0` and `1`:
`∑_{k<n+2} C(n+1,k)·f(k) = ∑_{k<n+1} C(n,k)·f(k) + ∑_{k<n+1} C(n,k)·f(k+1)`.

This is Pascal's rule `C(n+1,k+1) = C(n,k) + C(n,k+1)` summed against `f`, with
the boundary terms (`C(n+1,0) = C(n,0) = 1` and `C(n,n+1) = 0`) reconciled by the
first-term / last-term range peels. -/
theorem pascal_conv (f : ℕ → ℕ) (n : ℕ) :
    ∑ k ∈ range (n + 2), (n + 1).choose k * f k
      = (∑ k ∈ range (n + 1), n.choose k * f k)
        + ∑ k ∈ range (n + 1), n.choose k * f (k + 1) := by
  -- Peel the `k = 0` term off the left sum and reindex the rest by `k ↦ k+1`.
  rw [Finset.sum_range_succ' (fun k => (n + 1).choose k * f k) (n + 1)]
  -- Pascal's rule on each reindexed coefficient, then distribute the product.
  simp only [Nat.choose_succ_succ' n, Nat.choose_zero_right, one_mul, add_mul]
  rw [Finset.sum_add_distrib]
  -- Right-hand side: peel the `k = 0` term off `∑ C(n,k)·f(k)` in the same way.
  rw [Finset.sum_range_succ' (fun k => n.choose k * f k) n, Nat.choose_zero_right, one_mul]
  -- The `C(n, k+1)·f(k+1)` sum over `range (n+1)` has a vanishing top term
  -- `C(n, n+1) = 0`, so it agrees with the same sum over `range n`.
  rw [Finset.sum_range_succ (fun k => n.choose (k + 1) * f (k + 1)) n,
      Nat.choose_succ_self n, zero_mul, add_zero]
  ring

/-- **The Fibonacci binomial transform.** For all `n, m`,
`∑_{k≤n} C(n,k)·Fₘ₊ₖ = F₂ₙ₊ₘ`: the binomial-weighted sum of the length-`(n+1)`
Fibonacci window `Fₘ, Fₘ₊₁, …, Fₘ₊ₙ` collapses to the single Fibonacci number at
the doubled-and-shifted index `2n + m`.

Proved by induction on `n` with `m` universally quantified. The step rewrites the
`C(n+1, ·)` sum via `pascal_conv` into the two `C(n, ·)` sums at offsets `m` and
`m+1`, applies the induction hypothesis to each (yielding `F₂ₙ₊ₘ + F₂ₙ₊ₘ₊₁`), and
contracts with the recurrence `Nat.fib_add_two`. -/
theorem fib_binom_transform (n m : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k * Nat.fib (m + k) = Nat.fib (2 * n + m) := by
  induction n generalizing m with
  | zero => simp
  | succ p ih =>
    -- LHS is the `C(p+1, ·)` binomial sum over `range (p+2)`.
    have hconv := pascal_conv (fun k => Nat.fib (m + k)) p
    -- Reindex the offset-1 sum: `Fₘ₊₍ₖ₊₁₎ = F₍ₘ₊₁₎₊ₖ`.
    have hshift : (∑ k ∈ range (p + 1), p.choose k * Nat.fib (m + (k + 1)))
        = ∑ k ∈ range (p + 1), p.choose k * Nat.fib ((m + 1) + k) := by
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      omega
    calc
      ∑ k ∈ range (p + 1 + 1), (p + 1).choose k * Nat.fib (m + k)
          = (∑ k ∈ range (p + 1), p.choose k * Nat.fib (m + k))
            + ∑ k ∈ range (p + 1), p.choose k * Nat.fib (m + (k + 1)) := hconv
      _ = Nat.fib (2 * p + m) + Nat.fib (2 * p + (m + 1)) := by
            rw [hshift, ih m, ih (m + 1)]
      _ = Nat.fib (2 * (p + 1) + m) := by
            have e : 2 * p + (m + 1) = (2 * p + m) + 1 := by omega
            have e2 : 2 * (p + 1) + m = (2 * p + m) + 2 := by omega
            rw [e, e2, Nat.fib_add_two]

/-- **The binomial transform of the Fibonacci sequence is the even-indexed
Fibonacci sequence.** The `m = 0` headline case: `∑_{k≤n} C(n,k)·Fₖ = F₂ₙ`. -/
theorem fib_binom_transform_zero (n : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k * Nat.fib k = Nat.fib (2 * n) := by
  have h := fib_binom_transform n 0
  simpa using h

end FibonacciIdentitiesOQ06OQ01
