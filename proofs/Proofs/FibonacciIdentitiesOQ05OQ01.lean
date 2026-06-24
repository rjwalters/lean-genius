import Mathlib

/-!
# Weighted and alternating refinements of the Fibonacci product-staircase

The parent file `FibonacciIdentitiesOQ05.lean` records the **product-sum** identity
`F₀F₁ + F₁F₂ + ⋯ + FₙFₙ₊₁ = Fₙ₊₁² − [n even]` — a parity-governed "staircase" of
consecutive Fibonacci products. Its open question asks for the two natural refinements:
the **weighted** sum `∑ k FₖFₖ₊₁` and the **alternating** sum `∑ (−1)ᵏ FₖFₖ₊₁`.

This entry settles both, and in doing so exposes a genuine asymmetry between them.

* `fib_cassini_sub` — Cassini in the shape we need: `Fₙ₊₁² − Fₙ₊₁Fₙ − Fₙ² = (−1)ⁿ`.
  (Mathlib does not record Cassini for `Nat.fib`; we prove it by a one-line induction.)

* `fib_weighted_prod_sum` — the **weighted sum has a clean closed form**:
  `2·∑_{k≤n} k FₖFₖ₊₁ = 2n Fₙ₊₁² − 2 Fₙ Fₙ₊₁ + (if n even then −n else n+1)`.
  Proved by induction; the step collapses via Cassini. The overall factor `2` keeps the
  parity correction an honest integer (it is `(−1)ⁿ⁺¹⌈n/2⌉` in disguise).

* `fib_alt_double_index_sum` — the clean **alternating** companion telescopes to a single
  product: `∑_{k≤n} (−1)ᵏ F₂ₖ = (−1)ⁿ Fₙ Fₙ₊₁`. Here `F₂ₖ` is the natural "alternating
  Fibonacci product" (`F₂ₖ = 2FₖFₖ₊₁ − Fₖ²`), and the proof is a pure ring step off the
  index-addition formula `F_{2k+2} = Fₖ Fₖ₊₁ + Fₖ₊₁ Fₖ₊₂`.

* `fib_two_mul_id` / `fib_alt_prod_sum_reduction` — the literal alternating *product* sum,
  by contrast, does **not** collapse to a single product. Using `2 FₖFₖ₊₁ = F₂ₖ + Fₖ²` we
  get `2·∑ (−1)ᵏ FₖFₖ₊₁ = (−1)ⁿ Fₙ Fₙ₊₁ + ∑ (−1)ᵏ Fₖ²`, where the residual alternating
  *square* sum is the irreducible remainder. So the alternating refinement is parity
  governed but, unlike the plain product sum, carries an irreducible alternating-square tail.

No axioms, no `native_decide`, no sorries.
-/

namespace FibonacciIdentitiesOQ05OQ01

open Finset

/-- **Cassini's identity**, in subtractive integer form:
`Fₙ₊₁² − Fₙ₊₁·Fₙ − Fₙ² = (−1)ⁿ`. Proved by induction off `Nat.fib_add_two`. -/
theorem fib_cassini_sub (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib (n + 1) * Nat.fib n - (Nat.fib n) ^ 2 = (-1) ^ n := by
  induction n with
  | zero => simp [Nat.fib]
  | succ n ih =>
    have hrec : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
      have h := Nat.fib_add_two (n := n)
      exact_mod_cast h
    have hsign : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by rw [pow_succ]; ring
    rw [hsign, show n + 1 + 1 = n + 2 from rfl, hrec]
    linear_combination -ih

/-- **Weighted product-sum** (closed form).
`2·(0·F₀F₁ + 1·F₁F₂ + ⋯ + n·FₙFₙ₊₁) = 2n Fₙ₊₁² − 2 Fₙ Fₙ₊₁ + (if n even then −n else n+1)`.

The scaling by `2` keeps the parity correction an integer; dividing by `2` gives
`∑ = n Fₙ₊₁² − Fₙ Fₙ₊₁ + (−1)ⁿ⁺¹⌈n/2⌉`. -/
theorem fib_weighted_prod_sum (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (k : ℤ) * Nat.fib k * Nat.fib (k + 1)
      = 2 * n * (Nat.fib (n + 1)) ^ 2 - 2 * Nat.fib n * Nat.fib (n + 1)
        + (if Even n then -(n : ℤ) else (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, show n + 1 + 1 = n + 2 from rfl]
    have hrec : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
      have h := Nat.fib_add_two (n := n); exact_mod_cast h
    have hcass := fib_cassini_sub n
    rw [hrec]
    rcases Nat.even_or_odd n with hn | hn
    · -- n even, so n+1 is odd; (−1)ⁿ = 1
      have hpow : (-1 : ℤ) ^ n = 1 := hn.neg_one_pow
      have hne : ¬ Even (n + 1) := by simp [Nat.even_add_one, hn]
      rw [if_pos hn, if_neg hne]
      rw [hpow] at hcass
      push_cast
      linear_combination (2 * (n : ℤ) + 2) * hcass
    · -- n odd, so n+1 is even; (−1)ⁿ = −1
      have hpow : (-1 : ℤ) ^ n = -1 := hn.neg_one_pow
      have hne : Even (n + 1) := hn.add_one
      rw [if_neg (by simpa [Nat.not_even_iff_odd] using hn), if_pos hne]
      rw [hpow] at hcass
      push_cast
      linear_combination (2 * (n : ℤ) + 2) * hcass

/-- **Alternating double-index sum** (clean closed form).
`∑_{k≤n} (−1)ᵏ F₂ₖ = (−1)ⁿ Fₙ Fₙ₊₁`. The step is a pure ring identity once the
index-addition formula `F_{2(n+1)} = Fₙ Fₙ₊₁ + Fₙ₊₁ Fₙ₊₂` is supplied. -/
theorem fib_alt_double_index_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * Nat.fib (2 * k)
      = (-1) ^ n * Nat.fib n * Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hdbl : (Nat.fib (2 * (n + 1)) : ℤ)
        = Nat.fib n * Nat.fib (n + 1) + Nat.fib (n + 1) * Nat.fib (n + 2) := by
      have h := Nat.fib_add n (n + 1)
      rw [show n + (n + 1) + 1 = 2 * (n + 1) from by ring] at h
      exact_mod_cast h
    have hsign : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by rw [pow_succ]; ring
    rw [hdbl, hsign, show n + 1 + 1 = n + 2 from rfl]
    ring

/-- The doubling identity `2 FₖFₖ₊₁ = F₂ₖ + Fₖ²` (integer form), from `Nat.fib_two_mul`. -/
theorem fib_two_mul_id (k : ℕ) :
    2 * (Nat.fib k : ℤ) * Nat.fib (k + 1) = Nat.fib (2 * k) + (Nat.fib k) ^ 2 := by
  have hle : Nat.fib k ≤ 2 * Nat.fib (k + 1) := by
    have hm : Nat.fib k ≤ Nat.fib (k + 1) := Nat.fib_mono (Nat.le_succ k)
    omega
  have h := Nat.fib_two_mul k
  zify [hle] at h
  linear_combination -h

/-- **Alternating product-sum reduction.** The literal alternating product sum reduces to
the clean alternating double-index sum plus an irreducible alternating-square remainder:
`2·∑_{k≤n} (−1)ᵏ FₖFₖ₊₁ = (−1)ⁿ Fₙ Fₙ₊₁ + ∑_{k≤n} (−1)ᵏ Fₖ²`. -/
theorem fib_alt_prod_sum_reduction (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * Nat.fib k * Nat.fib (k + 1)
      = (-1) ^ n * Nat.fib n * Nat.fib (n + 1)
        + ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (Nat.fib k : ℤ) ^ 2 := by
  rw [Finset.mul_sum, ← fib_alt_double_index_sum n, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hk := fib_two_mul_id k
  linear_combination (-1 : ℤ) ^ k * hk

end FibonacciIdentitiesOQ05OQ01
