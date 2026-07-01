import Mathlib

/-!
# Gibonacci product-sum identity: the parity constant is a discriminant

The parent entry `FibonacciIdentitiesOQ05.lean` proves the Fibonacci
*product-sum* identity
`Fₙ₊₁² = (F₀F₁ + F₁F₂ + ⋯ + FₙFₙ₊₁) + [n even]`,
where the correction term `[n even]` toggles between `1` (even `n`) and `0`
(odd `n`).

This entry answers the open follow-up: **what happens for a general Gibonacci
(Horadam) sequence** `G` obeying the Fibonacci recurrence
`Gₙ₊₂ = Gₙ₊₁ + Gₙ` with arbitrary seeds `G₀, G₁`?  The answer exposes the
`[n even]` toggle of the Fibonacci case as a shadow of the sequence's
**discriminant**

`D := G₁² − G₀G₁ − G₀²`,

the invariant governing the generalized Cassini identity
`Gₙ₊₁² − GₙGₙ₊₂ = (−1)ⁿ · D`.  The unified closed form is

`Gₙ₊₁² = (∑_{i≤n} GᵢGᵢ₊₁) + G₀² + [n even] · D`.               (`gib_prod_sum`)

Everything is stated over `ℤ` because the correction term is genuinely signed
for seeds other than the Fibonacci `(0, 1)`.

## Specializations

* **Fibonacci** `(G₀, G₁) = (0, 1)`: `D = 1`, `G₀² = 0`, recovering the parent
  identity `Fₙ₊₁² = ∑ FᵢFᵢ₊₁ + [n even]`  (`fib_prod_sum_int`).
* **Lucas** `(G₀, G₁) = (2, 1)`: `D = 1 − 2 − 4 = −5` — the discriminant of
  `x² − x − 1` scaled by the Lucas normalization.  The correction term is
  `4 − 5·[n even]`, i.e. `−1` for even `n` and `4` for odd `n`
  (`lucas_prod_sum`).

The engine is the generalized Cassini identity `gib_cassini`, proved by a
one-line `linear_combination` induction off the recurrence, and the main
identity is a single induction whose step is closed by `linear_combination`
once Cassini supplies the quadratic relation.

No axioms, no `native_decide`, no sorries.
-/

namespace FibonacciIdentitiesOQ05OQ02

open Finset

section Generic

variable (G : ℕ → ℤ) (hrec : ∀ n, G (n + 2) = G (n + 1) + G n)

include hrec

/-- **Generalized Cassini / Catalan identity.**
For any sequence obeying `Gₙ₊₂ = Gₙ₊₁ + Gₙ`,
`Gₙ₊₁² − Gₙ·Gₙ₊₂ = (−1)ⁿ · (G₁² − G₀G₁ − G₀²)`.
The bracketed constant is the sequence's *discriminant* `D`; it is the
translation-invariant of the recurrence. -/
theorem gib_cassini (n : ℕ) :
    G (n + 1) ^ 2 - G n * G (n + 2)
      = (-1) ^ n * (G 1 ^ 2 - G 0 * G 1 - G 0 ^ 2) := by
  induction n with
  | zero =>
    have h0 := hrec 0
    -- G 2 = G 1 + G 0
    rw [h0]; ring
  | succ k ih =>
    have h1 := hrec k          -- G (k+2) = G (k+1) + G k
    have h2 := hrec (k + 1)    -- G (k+3) = G (k+2) + G (k+1)
    -- Normalize the successor indices appearing in the goal.
    show G (k + 2) ^ 2 - G (k + 1) * G (k + 3)
        = (-1) ^ (k + 1) * (G 1 ^ 2 - G 0 * G 1 - G 0 ^ 2)
    linear_combination -ih + G (k + 2) * h1 - G (k + 1) * h2

/-- **Gibonacci product-sum identity** (unified closed form).
`Gₙ₊₁² = (∑_{i=0}^{n} GᵢGᵢ₊₁) + G₀² + [n even]·D`, where `D = G₁²−G₀G₁−G₀²`.
The parity toggle of the Fibonacci case is exactly the discriminant `D`. -/
theorem gib_prod_sum (n : ℕ) :
    G (n + 1) ^ 2
      = (∑ i ∈ Finset.range (n + 1), G i * G (i + 1))
        + G 0 ^ 2
        + (if Even n then (G 1 ^ 2 - G 0 * G 1 - G 0 ^ 2) else 0) := by
  induction n with
  | zero =>
    rw [if_pos (by decide : Even 0), Finset.sum_range_one]
    ring
  | succ k ih =>
    rw [Finset.sum_range_succ, show k + 1 + 1 = k + 2 from rfl]
    have hc := gib_cassini G hrec k
    have h1 := hrec k          -- G (k+2) = G (k+1) + G k
    rcases Nat.even_or_odd k with hk | hk
    · -- k even ⇒ k+1 odd
      have hodd : ¬ Even (k + 1) := by simp [Nat.even_add_one, hk]
      rw [if_pos hk] at ih
      rw [if_neg hodd]
      -- ih : G(k+1)^2 = S_k + G0^2 + D
      -- hc : G(k+1)^2 - G k * G(k+2) = D    (since (-1)^k = 1)
      rw [hk.neg_one_pow] at hc
      -- Goal: G(k+2)^2 = (S_k + G(k+1)*G(k+2)) + G0^2 + 0
      linear_combination ih - hc + G (k + 2) * h1
    · -- k odd ⇒ k+1 even
      have heven : Even (k + 1) := hk.add_one
      rw [if_neg (by simpa [Nat.not_even_iff_odd] using hk)] at ih
      rw [if_pos heven]
      rw [hk.neg_one_pow] at hc
      -- hc : G(k+1)^2 - G k * G(k+2) = -D
      linear_combination ih - hc + G (k + 2) * h1

/-- Even branch: for even `n`,
`∑_{i≤n} GᵢGᵢ₊₁ = Gₙ₊₁² − G₀² − D`. -/
theorem gib_prod_sum_even {n : ℕ} (hn : Even n) :
    (∑ i ∈ Finset.range (n + 1), G i * G (i + 1))
      = G (n + 1) ^ 2 - G 0 ^ 2 - (G 1 ^ 2 - G 0 * G 1 - G 0 ^ 2) := by
  have h := gib_prod_sum G hrec n
  rw [if_pos hn] at h
  linarith [h]

/-- Odd branch: for odd `n`,
`∑_{i≤n} GᵢGᵢ₊₁ = Gₙ₊₁² − G₀²`. -/
theorem gib_prod_sum_odd {n : ℕ} (hn : Odd n) :
    (∑ i ∈ Finset.range (n + 1), G i * G (i + 1))
      = G (n + 1) ^ 2 - G 0 ^ 2 := by
  have h := gib_prod_sum G hrec n
  rw [if_neg (by simpa [Nat.not_even_iff_odd] using hn)] at h
  linarith [h]

end Generic

/-! ## Fibonacci specialization: recovering the parent identity -/

/-- The Fibonacci sequence as a `ℤ`-valued Gibonacci sequence. -/
theorem fib_hrec : ∀ n, (Nat.fib (n + 2) : ℤ) = Nat.fib (n + 1) + Nat.fib n := by
  intro n; rw [Nat.fib_add_two]; push_cast; ring

/-- **Fibonacci product-sum** (integer form), recovering the parent entry:
`Fₙ₊₁² = ∑ FᵢFᵢ₊₁ + [n even]`.  Here `D = 1` and `G₀² = 0`. -/
theorem fib_prod_sum_int (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2
      = (∑ i ∈ Finset.range (n + 1), (Nat.fib i : ℤ) * Nat.fib (i + 1))
        + (if Even n then 1 else 0) := by
  have h := gib_prod_sum (fun n => (Nat.fib n : ℤ)) fib_hrec n
  simp only [Nat.fib_zero, Nat.fib_one, Nat.cast_zero, Nat.cast_one] at h
  simpa using h

/-! ## Lucas specialization: the discriminant becomes `−5` -/

/-- The pair `(Lₙ, Lₙ₊₁)`, computed by structural recursion. -/
def lucasPair : ℕ → ℤ × ℤ
  | 0 => (2, 1)
  | n + 1 => ((lucasPair n).2, (lucasPair n).1 + (lucasPair n).2)

/-- The Lucas numbers as a `ℤ`-valued sequence: `L₀ = 2`, `L₁ = 1`. -/
def lucasZ (n : ℕ) : ℤ := (lucasPair n).1

@[simp] theorem lucasZ_zero : lucasZ 0 = 2 := rfl
@[simp] theorem lucasZ_one : lucasZ 1 = 1 := rfl

theorem lucasZ_hrec : ∀ n, lucasZ (n + 2) = lucasZ (n + 1) + lucasZ n := by
  intro n
  simp only [lucasZ, lucasPair]
  ring

/-- **Lucas product-sum identity.**  For the Lucas numbers the discriminant is
`D = 1 − 2 − 4 = −5`, so the correction term `G₀² + [n even]·D` equals
`4 + (if Even n then -5 else 0)`, i.e. `−1` for even `n`, `4` for odd `n`. -/
theorem lucas_prod_sum (n : ℕ) :
    lucasZ (n + 1) ^ 2
      = (∑ i ∈ Finset.range (n + 1), lucasZ i * lucasZ (i + 1))
        + 4 + (if Even n then (-5) else 0) := by
  have h := gib_prod_sum lucasZ lucasZ_hrec n
  simp only [lucasZ_zero, lucasZ_one] at h
  rw [h]
  norm_num

end FibonacciIdentitiesOQ05OQ02
