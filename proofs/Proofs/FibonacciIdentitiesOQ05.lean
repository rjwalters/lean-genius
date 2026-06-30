import Mathlib

/-!
# Fibonacci product-sum identity (the "staircase of consecutive products")

The parent file `FibonacciIdentities.lean` records the classical **sum of squares**
telescoping identity `F₀² + F₁² + ⋯ + Fₙ² = Fₙ · Fₙ₊₁`. This entry supplies the
*product* analogue: the partial sums of the **consecutive products** `Fₖ · Fₖ₊₁`.

Unlike the sum-of-squares identity, the product sum is **parity governed**:

* `fib_prod_sum` — the unified closed form, stated additively to stay inside `ℕ`:
  `Fₙ₊₁² = (F₀F₁ + F₁F₂ + ⋯ + FₙFₙ₊₁) + [n even]`,
  where `[n even]` contributes `1` when `n` is even and `0` when `n` is odd.

* `fib_prod_sum_even` / `fib_prod_sum_odd` — the two explicit branches:
  `∑ = Fₙ₊₁² − 1` for even `n`, and `∑ = Fₙ₊₁²` for odd `n`.

The engine is **Cassini's identity** `Fₙ₊₂² = Fₙ₊₁·Fₙ₊₃ + (−1)ⁿ⁺¹`, which Mathlib does
not record for `Nat.fib`; we prove it here in `ℤ` by a short induction off the defining
recurrence `Nat.fib_add_two`, then read off the two natural-number Cassini specializations
by parity. The main identity is then a single induction whose step is closed by `omega`
once Cassini supplies the quadratic relation between `Fₙ₊₁²` and `Fₙ₊₂²`.

No axioms, no `native_decide`, no sorries.
-/

namespace FibonacciIdentitiesOQ05

open Finset

/-- **Cassini's identity** (integer form).
`Fₙ₊₂² = Fₙ₊₁ · Fₙ₊₃ + (−1)ⁿ⁺¹`. Proved by induction off `Nat.fib_add_two`. -/
theorem fib_cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) ^ 2 = Nat.fib (n + 1) * Nat.fib (n + 3) + (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num [Nat.fib]
  | succ k ih =>
    have e1 : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      rw [show k + 3 = (k + 1) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
    have e2 : (Nat.fib (k + 4) : ℤ) = Nat.fib (k + 2) + Nat.fib (k + 3) := by
      rw [show k + 4 = (k + 2) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
    -- Goal: fib (k+3)^2 = fib (k+2) * fib (k+4) + (-1)^(k+2)
    rw [show k + 1 + 3 = k + 4 from rfl, show k + 1 + 2 = k + 3 from rfl,
      show k + 1 + 1 = k + 2 from rfl, e2]
    have hsign : (-1 : ℤ) ^ (k + 2) = -((-1) ^ (k + 1)) := by ring
    rw [hsign]
    linear_combination -ih + (Nat.fib (k + 3) : ℤ) * e1

/-- Even-index Cassini specialization (natural numbers):
for even `k` the index `k+1` is odd, so `Fₖ₊₁ · Fₖ₊₃ = Fₖ₊₂² + 1`. -/
theorem cassini_nat_even {k : ℕ} (hk : Even k) :
    Nat.fib (k + 1) * Nat.fib (k + 3) = Nat.fib (k + 2) ^ 2 + 1 := by
  have h := fib_cassini k
  rw [(hk.add_one).neg_one_pow] at h
  -- h : (Nat.fib (k+2) : ℤ)^2 = Nat.fib (k+1) * Nat.fib (k+3) + (-1)
  zify
  linarith [h]

/-- Odd-index Cassini specialization (natural numbers):
for odd `k` the index `k+1` is even, so `Fₖ₊₂² = Fₖ₊₁ · Fₖ₊₃ + 1`. -/
theorem cassini_nat_odd {k : ℕ} (hk : Odd k) :
    Nat.fib (k + 2) ^ 2 = Nat.fib (k + 1) * Nat.fib (k + 3) + 1 := by
  have h := fib_cassini k
  rw [(hk.add_one).neg_one_pow] at h
  -- h : (Nat.fib (k+2) : ℤ)^2 = Nat.fib (k+1) * Nat.fib (k+3) + 1
  zify
  linarith [h]

/-- **Fibonacci product-sum identity** (unified, additive form).
`Fₙ₊₁² = (F₀F₁ + F₁F₂ + ⋯ + FₙFₙ₊₁) + [n even]`. -/
theorem fib_prod_sum (n : ℕ) :
    Nat.fib (n + 1) ^ 2
      = (∑ i ∈ Finset.range (n + 1), Nat.fib i * Nat.fib (i + 1))
        + (if Even n then 1 else 0) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have he1 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      rw [show k + 3 = (k + 1) + 2 from rfl, Nat.fib_add_two]
    rcases Nat.even_or_odd k with hk | hk
    · -- k even, so k+1 is odd
      have hc := cassini_nat_even hk
      rw [he1, mul_add, ← pow_two] at hc
      -- hc : Fₖ₊₁² + Fₖ₊₁·Fₖ₊₂ = Fₖ₊₂² + 1
      rw [if_pos hk] at ih
      have hodd : ¬ Even (k + 1) := by simp [Nat.even_add_one, hk]
      rw [show k + 1 + 1 = k + 2 from rfl, if_neg hodd]
      omega
    · -- k odd, so k+1 is even
      have hc := cassini_nat_odd hk
      rw [he1, mul_add, ← pow_two] at hc
      -- hc : Fₖ₊₂² = Fₖ₊₁² + Fₖ₊₁·Fₖ₊₂ + 1
      rw [if_neg (by simpa [Nat.not_even_iff_odd] using hk)] at ih
      have heven : Even (k + 1) := hk.add_one
      rw [show k + 1 + 1 = k + 2 from rfl, if_pos heven]
      omega

/-- Even branch: `F₀F₁ + ⋯ + FₙFₙ₊₁ = Fₙ₊₁² − 1` when `n` is even. -/
theorem fib_prod_sum_even {n : ℕ} (hn : Even n) :
    (∑ i ∈ Finset.range (n + 1), Nat.fib i * Nat.fib (i + 1)) = Nat.fib (n + 1) ^ 2 - 1 := by
  have h := fib_prod_sum n
  rw [if_pos hn] at h
  omega

/-- Odd branch: `F₀F₁ + ⋯ + FₙFₙ₊₁ = Fₙ₊₁²` when `n` is odd. -/
theorem fib_prod_sum_odd {n : ℕ} (hn : Odd n) :
    (∑ i ∈ Finset.range (n + 1), Nat.fib i * Nat.fib (i + 1)) = Nat.fib (n + 1) ^ 2 := by
  have h := fib_prod_sum n
  rw [if_neg (by simpa [Nat.not_even_iff_odd] using hn)] at h
  omega

end FibonacciIdentitiesOQ05
