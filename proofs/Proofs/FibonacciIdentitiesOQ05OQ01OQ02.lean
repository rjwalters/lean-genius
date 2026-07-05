import Mathlib

-- A few `push_cast` calls before `linear_combination` are flagged as no-ops by the
-- `unusedTactic` linter, but are in fact required to normalise `↑(n+1)` to `↑n + 1`.
set_option linter.unusedTactic false

/-!
# Weighted product-sum identities for the Gibonacci family (Fibonacci, Lucas, general)

The parent entry `FibonacciIdentitiesOQ05OQ01.lean` proves the **weighted product-sum**
closed form for consecutive Fibonacci numbers,
`2·∑_{k≤n} k FₖFₖ₊₁ = 2n Fₙ₊₁² − 2 FₙFₙ₊₁ + (if n even then −n else n+1)`,
where the correction term is governed by Cassini's identity
`Fₙ₊₁² − Fₙ₊₁Fₙ − Fₙ² = (−1)ⁿ`.

This entry **unifies** that fact across the whole Gibonacci family. A *Gibonacci*
sequence has the Fibonacci recurrence `Gₖ₊₂ = Gₖ₊₁ + Gₖ` but **arbitrary** initial
conditions `G₀ = a`, `G₁ = b`. Its Cassini-type invariant is the **discriminant**
`D = b² − ab − a²`, and everything the Fibonacci case does with the bare `(−1)ⁿ`
correction the general case does with `(−1)ⁿ·D`.

* `gib_cassini` — **generalized Cassini**: `Gₙ₊₁² − Gₙ₊₁Gₙ − Gₙ² = (−1)ⁿ (b² − ab − a²)`.
  A one-line induction; the step flips sign exactly as in the Fibonacci case, so the
  invariant is `(−1)ⁿ` times the fixed discriminant `D = b² − ab − a²`.

* `gib_weighted_prod_sum` — **generalized weighted product-sum** (closed form):
  `2·∑_{k≤n} k GₖGₖ₊₁ = 2n Gₙ₊₁² − 2 GₙGₙ₊₁ + 2ab + D·(if n even then −n else n+1)`.
  Proved by induction; the step collapses via `gib_cassini`. The extra constant `2ab`
  (absent in the Fibonacci case since `a = 0`) is the `n = 0` boundary value, and the
  parity correction picks up the discriminant factor `D`.

The two named specializations follow by substituting the initial conditions and reading
off the discriminant:

* Fibonacci `(a,b) = (0,1)`, `D = 1`: `gib 0 1 = Nat.fib` (`gib_zero_one_eq_fib`) recovers
  the parent identity `fib_weighted_prod_sum` verbatim.
* Lucas `(a,b) = (2,1)`, `D = −5`: `lucas_cassini` gives `Lₙ₊₁² − Lₙ₊₁Lₙ − Lₙ² = −5·(−1)ⁿ`
  and `lucas_weighted_prod_sum` gives
  `2·∑_{k≤n} k LₖLₖ₊₁ = 2n Lₙ₊₁² − 2 LₙLₙ₊₁ + 4 − 5·(if n even then −n else n+1)`.

This makes precise the claim in the open question that "the parity correction `(−1)ⁿ`
becomes the sequence discriminant `b² − ab − a²`."

No axioms, no `native_decide`, no sorries.
-/

namespace FibonacciIdentitiesOQ05OQ01OQ02

open Finset

/-- A **Gibonacci** sequence: the Fibonacci recurrence with arbitrary initial conditions
`G₀ = a`, `G₁ = b`. -/
def gib (a b : ℤ) : ℕ → ℤ
  | 0 => a
  | 1 => b
  | (n + 2) => gib a b (n + 1) + gib a b n

@[simp] lemma gib_zero (a b : ℤ) : gib a b 0 = a := rfl
@[simp] lemma gib_one (a b : ℤ) : gib a b 1 = b := rfl

/-- The defining recurrence, as a rewrite lemma. -/
lemma gib_add_two (a b : ℤ) (n : ℕ) :
    gib a b (n + 2) = gib a b (n + 1) + gib a b n := rfl

/-- **Generalized Cassini identity.** For any Gibonacci sequence with `G₀ = a`, `G₁ = b`,
`Gₙ₊₁² − Gₙ₊₁·Gₙ − Gₙ² = (−1)ⁿ·(b² − ab − a²)`.

The right-hand factor `b² − ab − a²` is the **discriminant** of the sequence; it is the
`n = 0` value of the left-hand side, and the induction step simply flips its sign. -/
theorem gib_cassini (a b : ℤ) (n : ℕ) :
    (gib a b (n + 1)) ^ 2 - gib a b (n + 1) * gib a b n - (gib a b n) ^ 2
      = (-1) ^ n * (b ^ 2 - a * b - a ^ 2) := by
  induction n with
  | zero => simp only [zero_add, gib_one, gib_zero]; ring
  | succ n ih =>
    have hsign : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by rw [pow_succ]; ring
    rw [hsign, show n + 1 + 1 = n + 2 from rfl, gib_add_two]
    linear_combination -ih

/-- **Generalized weighted product-sum** (closed form). For any Gibonacci sequence with
`G₀ = a`, `G₁ = b` and discriminant `D = b² − ab − a²`,
`2·(0·G₀G₁ + 1·G₁G₂ + ⋯ + n·GₙGₙ₊₁) = 2n Gₙ₊₁² − 2 GₙGₙ₊₁ + 2ab + D·(if n even then −n else n+1)`.

Specializes to the Fibonacci weighted sum (`a = 0`, `b = 1`, `D = 1`, so the `2ab` term
vanishes) and to the Lucas weighted sum (`a = 2`, `b = 1`, `D = −5`). -/
theorem gib_weighted_prod_sum (a b : ℤ) (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (k : ℤ) * gib a b k * gib a b (k + 1)
      = 2 * (n : ℤ) * (gib a b (n + 1)) ^ 2 - 2 * gib a b n * gib a b (n + 1)
        + 2 * a * b
        + (b ^ 2 - a * b - a ^ 2) * (if Even n then -(n : ℤ) else (n : ℤ) + 1) := by
  induction n with
  | zero =>
      rw [Finset.sum_range_one, if_pos (even_zero)]
      simp only [zero_add, gib_zero, gib_one, Nat.cast_zero, neg_zero, mul_zero, zero_mul]
      ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hcass := gib_cassini a b n
    rcases Nat.even_or_odd n with hn | hn
    · -- n even ⇒ (n+1) odd; Cassini gives +D
      have hodd : ¬ Even (n + 1) := by simp [Nat.even_add_one, hn]
      have hcass1 : (gib a b (n + 1)) ^ 2 - gib a b (n + 1) * gib a b n
          - (gib a b n) ^ 2 = b ^ 2 - a * b - a ^ 2 := by
        rw [hcass, hn.neg_one_pow, one_mul]
      rw [if_pos hn, if_neg hodd, show n + 1 + 1 = n + 2 from rfl, gib_add_two]
      push_cast
      linear_combination 2 * ((n : ℤ) + 1) * hcass1
    · -- n odd ⇒ (n+1) even; Cassini gives −D
      have hev : Even (n + 1) := hn.add_one
      have hne : ¬ Even n := by simpa [Nat.not_even_iff_odd] using hn
      have hcass1 : (gib a b (n + 1)) ^ 2 - gib a b (n + 1) * gib a b n
          - (gib a b n) ^ 2 = -(b ^ 2 - a * b - a ^ 2) := by
        rw [hcass, hn.neg_one_pow]; ring
      rw [if_neg hne, if_pos hev, show n + 1 + 1 = n + 2 from rfl, gib_add_two]
      push_cast
      linear_combination 2 * ((n : ℤ) + 1) * hcass1

/-! ## Fibonacci specialization (`a = 0`, `b = 1`, `D = 1`) -/

/-- The Gibonacci sequence with initial conditions `(0, 1)` is exactly `Nat.fib`. -/
theorem gib_zero_one_eq_fib : ∀ n, gib 0 1 n = (Nat.fib n : ℤ)
  | 0 => by simp
  | 1 => by simp
  | (n + 2) => by
      rw [gib_add_two, gib_zero_one_eq_fib (n + 1), gib_zero_one_eq_fib n, Nat.fib_add_two]
      push_cast; ring

/-- Recovering the parent identity `fib_weighted_prod_sum` as the `(0,1)` specialization:
`2·∑_{k≤n} k FₖFₖ₊₁ = 2n Fₙ₊₁² − 2 FₙFₙ₊₁ + (if n even then −n else n+1)`.
Here the discriminant is `1` and the boundary term `2ab` vanishes. -/
theorem fib_weighted_prod_sum (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (k : ℤ) * Nat.fib k * Nat.fib (k + 1)
      = 2 * (n : ℤ) * (Nat.fib (n + 1)) ^ 2 - 2 * Nat.fib n * Nat.fib (n + 1)
        + (if Even n then -(n : ℤ) else (n : ℤ) + 1) := by
  have h := gib_weighted_prod_sum 0 1 n
  simp only [gib_zero_one_eq_fib] at h
  linear_combination h

/-! ## Lucas specialization (`a = 2`, `b = 1`, `D = −5`) -/

/-- The **Lucas numbers** `L₀ = 2`, `L₁ = 1`, `Lₖ₊₂ = Lₖ₊₁ + Lₖ`, realized as the
Gibonacci sequence with initial conditions `(2, 1)`. -/
def lucas (n : ℕ) : ℤ := gib 2 1 n

@[simp] lemma lucas_zero : lucas 0 = 2 := rfl
@[simp] lemma lucas_one : lucas 1 = 1 := rfl

lemma lucas_add_two (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := rfl

/-- **Lucas Cassini identity.** `Lₙ₊₁² − Lₙ₊₁·Lₙ − Lₙ² = −5·(−1)ⁿ`; the discriminant of
the Lucas sequence is `b² − ab − a² = 1 − 2 − 4 = −5`. -/
theorem lucas_cassini (n : ℕ) :
    (lucas (n + 1)) ^ 2 - lucas (n + 1) * lucas n - (lucas n) ^ 2 = -5 * (-1) ^ n := by
  have h := gib_cassini 2 1 n
  simp only [lucas]
  linear_combination h

/-- **Lucas weighted product-sum** (closed form):
`2·∑_{k≤n} k LₖLₖ₊₁ = 2n Lₙ₊₁² − 2 LₙLₙ₊₁ + 4 − 5·(if n even then −n else n+1)`.
The boundary term is `2ab = 4` and the parity correction carries the discriminant `−5`. -/
theorem lucas_weighted_prod_sum (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (k : ℤ) * lucas k * lucas (k + 1)
      = 2 * (n : ℤ) * (lucas (n + 1)) ^ 2 - 2 * lucas n * lucas (n + 1)
        + 4 - 5 * (if Even n then -(n : ℤ) else (n : ℤ) + 1) := by
  have h := gib_weighted_prod_sum 2 1 n
  simp only [lucas]
  linear_combination h

end FibonacciIdentitiesOQ05OQ01OQ02
