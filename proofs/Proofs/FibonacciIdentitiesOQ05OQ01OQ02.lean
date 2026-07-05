import Mathlib

set_option linter.unusedTactic false

/-!
# Weighted product-sum identities for Lucas and Gibonacci sequences

The parent file `FibonacciIdentitiesOQ05OQ01.lean` proves the **weighted product-sum**
closed form for Fibonacci numbers:
`2·∑_{k≤n} k FₖFₖ₊₁ = 2n Fₙ₊₁² − 2 Fₙ Fₙ₊₁ + (if n even then −n else n+1)`.
Its open question asks to generalize this to Lucas numbers and to arbitrary **Gibonacci**
(generalized Fibonacci) sequences, and to see what the parity correction `±1` becomes.

## Answer
For any integer sequence `G` satisfying the Fibonacci recurrence `Gₙ₊₂ = Gₙ + Gₙ₊₁`, put
the **discriminant** `D := G₁² − G₁G₀ − G₀²`. Then:

* `gib_cassini` — Cassini generalizes verbatim with `D` in place of `1`:
  `Gₙ₊₁² − Gₙ₊₁Gₙ − Gₙ² = (−1)ⁿ · D`.

* `gib_weighted_prod_sum` — the weighted product-sum has the closed form
  `2·∑_{k≤n} k GₖGₖ₊₁ = 2n Gₙ₊₁² − 2 Gₙ Gₙ₊₁ + 2 G₀ G₁ + D·(if n even then −n else n+1)`.
  So the parity correction `±1` of the Fibonacci case is exactly `±D`: **the correction is
  governed by the discriminant**, plus a constant `2G₀G₁` coming from a nonzero initial seed.

## Specializations
* **Fibonacci** (`G₀=0, G₁=1`): `D = 1`, `2G₀G₁ = 0`, recovering the parent identity exactly
  (`fib_weighted_prod_sum` below).
* **Lucas** (`L₀=2, L₁=1`): `D = 1 − 2 − 4 = −5` (the Fibonacci–Lucas discriminant, the `5`
  under the `√5` of Binet's formula) and `2L₀L₁ = 4`, giving
  `2·∑ k LₖLₖ₊₁ = 2n Lₙ₊₁² − 2 Lₙ Lₙ₊₁ + 4 − 5·(if n even then −n else n+1)`
  (`lucas_weighted_prod_sum`), and Cassini `Lₙ₊₁² − Lₙ₊₁Lₙ − Lₙ² = −5·(−1)ⁿ`.

No axioms, no `native_decide`, no sorries.
-/

namespace FibonacciIdentitiesOQ05OQ01OQ02

open Finset

section Gibonacci

variable (G : ℕ → ℤ) (hrec : ∀ n, G (n + 2) = G n + G (n + 1))

include hrec

/-- **Cassini for a Gibonacci sequence.** With discriminant `D = G₁² − G₁G₀ − G₀²`,
`Gₙ₊₁² − Gₙ₊₁Gₙ − Gₙ² = (−1)ⁿ · D`. Proved by induction off the recurrence; the Fibonacci
case (`D = 1`) is the classical Cassini identity. -/
theorem gib_cassini (n : ℕ) :
    G (n + 1) ^ 2 - G (n + 1) * G n - (G n) ^ 2
      = (-1) ^ n * (G 1 ^ 2 - G 1 * G 0 - (G 0) ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr : G (n + 1 + 1) = G n + G (n + 1) := hrec n
    have hsign : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by rw [pow_succ]; ring
    rw [hsign, hr]
    linear_combination -ih

/-- **Weighted product-sum for a Gibonacci sequence** (closed form).
`2·∑_{k≤n} k GₖGₖ₊₁ = 2n Gₙ₊₁² − 2 Gₙ Gₙ₊₁ + 2 G₀ G₁ + D·(if n even then −n else n+1)`,
where `D = G₁² − G₁G₀ − G₀²`. The parity correction of the Fibonacci case is scaled by the
discriminant `D`; the constant `2 G₀ G₁` is the contribution of a nonzero seed. -/
theorem gib_weighted_prod_sum (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (k : ℤ) * G k * G (k + 1)
      = 2 * n * (G (n + 1)) ^ 2 - 2 * G n * G (n + 1)
        + 2 * G 0 * G 1
        + (G 1 ^ 2 - G 1 * G 0 - (G 0) ^ 2) * (if Even n then -(n : ℤ) else (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hr : G (n + 1 + 1) = G n + G (n + 1) := hrec n
    have hcass := gib_cassini G hrec n
    rcases Nat.even_or_odd n with hn | hn
    · -- n even ⇒ (n+1) odd
      have hodd : ¬ Even (n + 1) := by simp [Nat.even_add_one, hn]
      have hcass1 : G (n + 1) ^ 2 - G (n + 1) * G n - (G n) ^ 2
          = (G 1 ^ 2 - G 1 * G 0 - (G 0) ^ 2) := by
        rw [hcass, hn.neg_one_pow]; ring
      rw [if_pos hn, if_neg hodd, hr]
      push_cast
      linear_combination 2 * ((n : ℤ) + 1) * hcass1
    · -- n odd ⇒ (n+1) even
      have hev : Even (n + 1) := hn.add_one
      have hne : ¬ Even n := by simpa [Nat.not_even_iff_odd] using hn
      have hcass1 : G (n + 1) ^ 2 - G (n + 1) * G n - (G n) ^ 2
          = -(G 1 ^ 2 - G 1 * G 0 - (G 0) ^ 2) := by
        rw [hcass, hn.neg_one_pow]; ring
      rw [if_neg hne, if_pos hev, hr]
      push_cast
      linear_combination 2 * ((n : ℤ) + 1) * hcass1

end Gibonacci

/-! ## Fibonacci recovery (`D = 1`, seed `2G₀G₁ = 0`) -/

/-- The integer-cast Fibonacci sequence satisfies the Gibonacci recurrence. -/
private theorem fib_hrec (n : ℕ) :
    ((Nat.fib (n + 2) : ℤ)) = (Nat.fib n : ℤ) + (Nat.fib (n + 1) : ℤ) := by
  have h := Nat.fib_add_two (n := n)
  exact_mod_cast h

/-- **Fibonacci weighted product-sum**, recovered from the Gibonacci formula: the
discriminant is `D = 1` and the seed constant `2 F₀ F₁ = 0`, so the correction is `±1`. -/
theorem fib_weighted_prod_sum (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (k : ℤ) * Nat.fib k * Nat.fib (k + 1)
      = 2 * n * (Nat.fib (n + 1)) ^ 2 - 2 * Nat.fib n * Nat.fib (n + 1)
        + (if Even n then -(n : ℤ) else (n + 1)) := by
  have h := gib_weighted_prod_sum (fun m => (Nat.fib m : ℤ)) fib_hrec n
  simp only [Nat.fib_zero, Nat.fib_one, Nat.cast_zero, Nat.cast_one] at h
  linear_combination h

/-! ## Lucas numbers (`D = −5`, seed `2L₀L₁ = 4`) -/

/-- The **Lucas numbers** `L₀ = 2, L₁ = 1, Lₙ₊₂ = Lₙ + Lₙ₊₁`, as an integer sequence. -/
def Luc : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 2) => Luc n + Luc (n + 1)

@[simp] theorem Luc_zero : Luc 0 = 2 := rfl
@[simp] theorem Luc_one : Luc 1 = 1 := rfl

theorem Luc_rec (n : ℕ) : Luc (n + 2) = Luc n + Luc (n + 1) := by
  cases n <;> rfl

/-- **Cassini for Lucas numbers:** `Lₙ₊₁² − Lₙ₊₁Lₙ − Lₙ² = (−1)ⁿ · (−5)`. The Fibonacci
`±1` is replaced by the discriminant `−5`. -/
theorem lucas_cassini (n : ℕ) :
    Luc (n + 1) ^ 2 - Luc (n + 1) * Luc n - (Luc n) ^ 2 = (-1) ^ n * (-5) := by
  have h := gib_cassini Luc Luc_rec n
  rw [Luc_zero, Luc_one] at h
  linear_combination h

/-- **Lucas weighted product-sum:**
`2·∑_{k≤n} k LₖLₖ₊₁ = 2n Lₙ₊₁² − 2 Lₙ Lₙ₊₁ + 4 − 5·(if n even then −n else n+1)`.
The parity correction is scaled by the Lucas discriminant `D = −5`, with seed constant
`2 L₀ L₁ = 4`. -/
theorem lucas_weighted_prod_sum (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (k : ℤ) * Luc k * Luc (k + 1)
      = 2 * n * (Luc (n + 1)) ^ 2 - 2 * Luc n * Luc (n + 1)
        + 4 + (-5) * (if Even n then -(n : ℤ) else (n + 1)) := by
  have h := gib_weighted_prod_sum Luc Luc_rec n
  rw [Luc_zero, Luc_one] at h
  linear_combination h

end FibonacciIdentitiesOQ05OQ01OQ02
