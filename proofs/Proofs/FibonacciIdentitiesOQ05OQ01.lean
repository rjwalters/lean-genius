import Mathlib

-- A few `push_cast` calls before `linear_combination` are flagged as no-ops by the
-- `unusedTactic` linter, but are in fact required to normalise `↑(n+1)` to `↑n + 1`.
set_option linter.unusedTactic false

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
  Proved directly by induction; the step collapses via Cassini. The factor `2` keeps the
  correction term an honest integer (it is `(−1)ⁿ⁺¹⌈n/2⌉` after halving).

* `fib_alt_double_index_sum` — the clean **alternating** companion telescopes to a single
  product: `∑_{k≤n} (−1)ᵏ F₂ₖ = (−1)ⁿ Fₙ Fₙ₊₁`. Here `F₂ₖ` is the natural "alternating
  Fibonacci product" (`F₂ₖ = Fₖ·Lₖ`).

* `fib_alt_prod_sum_reduction` — the literal alternating *product* sum, by contrast, does
  **not** collapse to a single product. Using `2 FₖFₖ₊₁ = F₂ₖ + Fₖ²` we get
  `2·∑ (−1)ᵏ FₖFₖ₊₁ = (−1)ⁿ Fₙ Fₙ₊₁ + ∑ (−1)ᵏ Fₖ²`, where the residual alternating
  *square* sum is irreducible (no quadratic in `Fₙ, Fₙ₊₁, (−1)ⁿ` fits it, even after a
  parity split). So the alternating refinement is parity-governed but, unlike the plain
  product sum, carries an irreducible remainder.

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
      have h := Nat.fib_add_two (n := n); exact_mod_cast h
    have hsign : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by rw [pow_succ]; ring
    rw [hsign, show n + 1 + 1 = n + 2 from rfl, hrec]
    linear_combination -ih

/-- **Weighted product-sum** (closed form).
`2·(0·F₀F₁ + 1·F₁F₂ + ⋯ + n·FₙFₙ₊₁) = 2n Fₙ₊₁² − 2 Fₙ Fₙ₊₁ + (if n even then −n else n+1)`.

Dividing by `2` gives `∑ = n Fₙ₊₁² − Fₙ Fₙ₊₁ + (−1)ⁿ⁺¹⌈n/2⌉`; the scaling keeps the
parity correction an integer. -/
theorem fib_weighted_prod_sum (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (k : ℤ) * Nat.fib k * Nat.fib (k + 1)
      = 2 * n * (Nat.fib (n + 1)) ^ 2 - 2 * Nat.fib n * Nat.fib (n + 1)
        + (if Even n then -(n : ℤ) else (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hrec : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
      have h := Nat.fib_add_two (n := n); exact_mod_cast h
    have hcass := fib_cassini_sub n
    rcases Nat.even_or_odd n with hn | hn
    · -- n even ⇒ (n+1) odd
      have hodd : ¬ Even (n + 1) := by simp [Nat.even_add_one, hn]
      have hcass1 : (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib (n + 1) * Nat.fib n
          - (Nat.fib n) ^ 2 = 1 := hcass.trans hn.neg_one_pow
      rw [if_pos hn, if_neg hodd, show n + 1 + 1 = n + 2 from rfl, hrec]
      push_cast
      linear_combination 2 * ((n : ℤ) + 1) * hcass1
    · -- n odd ⇒ (n+1) even
      have hev : Even (n + 1) := hn.add_one
      have hne : ¬ Even n := by simpa [Nat.not_even_iff_odd] using hn
      have hcass1 : (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib (n + 1) * Nat.fib n
          - (Nat.fib n) ^ 2 = -1 := hcass.trans hn.neg_one_pow
      rw [if_neg hne, if_pos hev, show n + 1 + 1 = n + 2 from rfl, hrec]
      push_cast
      linear_combination 2 * ((n : ℤ) + 1) * hcass1

/-- **Alternating sum of even-indexed Fibonacci numbers** telescopes to a single product:
`∑_{k≤n} (−1)ᵏ F₂ₖ = (−1)ⁿ Fₙ Fₙ₊₁`. The step uses the addition formula
`F₂ₙ₊₂ = Fₙ₊₁(Fₙ + Fₙ₊₂)`. -/
theorem fib_alt_double_index_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (Nat.fib (2 * k))
      = (-1) ^ n * Nat.fib n * Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hadd : (Nat.fib (2 * (n + 1)) : ℤ)
        = Nat.fib (n + 1) * Nat.fib n + Nat.fib (n + 2) * Nat.fib (n + 1) := by
      have h := Nat.fib_add (n + 1) n
      rw [show n + 1 + n + 1 = 2 * (n + 1) from by ring] at h
      exact_mod_cast h
    have hsign : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by rw [pow_succ]; ring
    rw [hsign, hadd, show n + 1 + 1 = n + 2 from rfl]
    push_cast
    ring

/-- **Alternating product-sum reduction.**
`2·∑_{k≤n} (−1)ᵏ Fₖ Fₖ₊₁ = (−1)ⁿ Fₙ Fₙ₊₁ + ∑_{k≤n} (−1)ᵏ Fₖ²`.

The even-indexed part collapses (`fib_alt_double_index_sum`); the alternating *square*
sum that remains has no elementary single-product closed form, so the alternating product
sum does not telescope the way its non-alternating cousin does. -/
theorem fib_alt_prod_sum_reduction (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (Nat.fib k * Nat.fib (k + 1))
      = (-1) ^ n * Nat.fib n * Nat.fib (n + 1)
        + ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (Nat.fib k) ^ 2 := by
  have key : ∀ k ∈ Finset.range (n + 1),
      2 * ((-1 : ℤ) ^ k * (Nat.fib k * Nat.fib (k + 1)))
        = (-1) ^ k * (Nat.fib (2 * k)) + (-1) ^ k * (Nat.fib k) ^ 2 := by
    intro k _
    have hmono : Nat.fib k ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
    have hle : Nat.fib k ≤ 2 * Nat.fib (k + 1) := by omega
    have h2 : (Nat.fib (2 * k) : ℤ)
        = 2 * (Nat.fib k : ℤ) * Nat.fib (k + 1) - (Nat.fib k) ^ 2 := by
      have hnat := Nat.fib_two_mul k
      zify [hle] at hnat
      rw [hnat]; ring
    rw [h2]; ring
  rw [Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_add_distrib,
    fib_alt_double_index_sum]

end FibonacciIdentitiesOQ05OQ01
