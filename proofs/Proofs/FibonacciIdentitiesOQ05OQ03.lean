import Mathlib

/-!
# Fibonacci gap-two product-sum identity (`∑ Fₖ Fₖ₊₂`)

The parent file `FibonacciIdentitiesOQ05.lean` records the **consecutive** product sum
`∑ Fₖ Fₖ₊₁` and its parity-governed closed form `Fₙ₊₁²` (up to the constant `[n even]`).
This entry answers the parent's open question for the **gap-two** companion:

> Prove the companion identity for products at a fixed gap, `∑ Fₖ Fₖ₊₂`,
> and relate its closed form to `Fₙ₊₁ Fₙ₊₂`.

The headline result is

* `fib_gap_two_prod_sum` — the unified closed form, stated additively to stay inside `ℕ`:
  `Fₙ₊₁ · Fₙ₊₂ = (F₀F₂ + F₁F₃ + ⋯ + FₙFₙ₊₂) + [n even]`,
  where `[n even]` contributes `1` for even `n` and `0` for odd `n`.

* `fib_gap_two_even` / `fib_gap_two_odd` — the two explicit branches:
  `∑ = Fₙ₊₁Fₙ₊₂ − 1` for even `n`, and `∑ = Fₙ₊₁Fₙ₊₂` for odd `n`.

Unlike the consecutive case, whose engine is Cassini's quadratic identity, the gap-two
recurrence step is governed by the **d'Ocagne / Catalan-type** identity
`Fₙ₊₁ Fₙ₊₄ − Fₙ₊₂ Fₙ₊₃ = (−1)ⁿ`, which we derive here (in `ℤ`) directly from Cassini
together with the defining recurrence `Fₙ₊₄ = Fₙ₊₂ + Fₙ₊₃`. From it we read off the
single linear product relation `Fₖ₊₂Fₖ₊₃ − Fₖ₊₁Fₖ₊₂ − Fₖ₊₁Fₖ₊₃ = (−1)ᵏ⁺¹` that closes
the induction step by `omega` (the three products enter linearly, as atoms).

No axioms, no `native_decide`, no sorries.
-/

namespace FibonacciIdentitiesOQ05OQ03

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
    rw [show k + 1 + 3 = k + 4 from rfl, show k + 1 + 2 = k + 3 from rfl,
      show k + 1 + 1 = k + 2 from rfl, e2]
    have hsign : (-1 : ℤ) ^ (k + 2) = -((-1) ^ (k + 1)) := by ring
    rw [hsign]
    linear_combination -ih + (Nat.fib (k + 3) : ℤ) * e1

/-- **d'Ocagne / Catalan-type identity** (integer form).
`Fₙ₊₁ · Fₙ₊₄ − Fₙ₊₂ · Fₙ₊₃ = (−1)ⁿ`. Derived from Cassini (at index `n+1`) and the
recurrences `Fₙ₊₃ = Fₙ₊₁ + Fₙ₊₂`, `Fₙ₊₄ = Fₙ₊₂ + Fₙ₊₃`. -/
theorem fib_docagne (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) * Nat.fib (n + 4) - Nat.fib (n + 2) * Nat.fib (n + 3)
      = (-1) ^ n := by
  have hc := fib_cassini (n + 1)
  have hsign : ((-1 : ℤ)) ^ (n + 1 + 1) = (-1) ^ n := by ring
  rw [hsign] at hc
  -- hc : (Fₙ₊₃)² = Fₙ₊₂ · Fₙ₊₄ + (−1)ⁿ
  have e3 : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
    rw [show n + 3 = (n + 1) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
  have e4 : (Nat.fib (n + 4) : ℤ) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
    rw [show n + 4 = (n + 2) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
  linear_combination hc - (Nat.fib (n + 4) : ℤ) * e3 + (Nat.fib (n + 3) : ℤ) * e4

/-- The linear product relation driving the gap-two recurrence step (integer form):
`Fₖ₊₂ · Fₖ₊₃ − Fₖ₊₁ · Fₖ₊₂ − Fₖ₊₁ · Fₖ₊₃ = (−1)ᵏ⁺¹`. -/
theorem fib_gap_rel (k : ℕ) :
    (Nat.fib (k + 2) : ℤ) * Nat.fib (k + 3)
        - Nat.fib (k + 1) * Nat.fib (k + 2) - Nat.fib (k + 1) * Nat.fib (k + 3)
      = (-1) ^ (k + 1) := by
  have hd := fib_docagne k
  have e4 : (Nat.fib (k + 4) : ℤ) = Nat.fib (k + 2) + Nat.fib (k + 3) := by
    rw [show k + 4 = (k + 2) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
  have hsign : ((-1 : ℤ)) ^ (k + 1) = -((-1) ^ k) := by ring
  rw [hsign]
  linear_combination -hd + (Nat.fib (k + 1) : ℤ) * e4

/-- Even-index specialization (natural numbers): for even `k`,
`Fₖ₊₁Fₖ₊₂ + Fₖ₊₁Fₖ₊₃ = Fₖ₊₂Fₖ₊₃ + 1`. -/
theorem gap_nat_even {k : ℕ} (hk : Even k) :
    Nat.fib (k + 1) * Nat.fib (k + 2) + Nat.fib (k + 1) * Nat.fib (k + 3)
      = Nat.fib (k + 2) * Nat.fib (k + 3) + 1 := by
  have h := fib_gap_rel k
  rw [(hk.add_one).neg_one_pow] at h
  -- h : Fₖ₊₂Fₖ₊₃ − Fₖ₊₁Fₖ₊₂ − Fₖ₊₁Fₖ₊₃ = −1
  zify
  linarith [h]

/-- Odd-index specialization (natural numbers): for odd `k`,
`Fₖ₊₂Fₖ₊₃ = Fₖ₊₁Fₖ₊₂ + Fₖ₊₁Fₖ₊₃ + 1`. -/
theorem gap_nat_odd {k : ℕ} (hk : Odd k) :
    Nat.fib (k + 2) * Nat.fib (k + 3)
      = Nat.fib (k + 1) * Nat.fib (k + 2) + Nat.fib (k + 1) * Nat.fib (k + 3) + 1 := by
  have h := fib_gap_rel k
  rw [(hk.add_one).neg_one_pow] at h
  -- h : Fₖ₊₂Fₖ₊₃ − Fₖ₊₁Fₖ₊₂ − Fₖ₊₁Fₖ₊₃ = 1
  zify
  linarith [h]

/-- **Fibonacci gap-two product-sum identity** (unified, additive form).
`Fₙ₊₁ · Fₙ₊₂ = (F₀F₂ + F₁F₃ + ⋯ + FₙFₙ₊₂) + [n even]`. -/
theorem fib_gap_two_prod_sum (n : ℕ) :
    Nat.fib (n + 1) * Nat.fib (n + 2)
      = (∑ i ∈ Finset.range (n + 1), Nat.fib i * Nat.fib (i + 2))
        + (if Even n then 1 else 0) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.even_or_odd k with hk | hk
    · -- k even, so k+1 is odd
      have hc := gap_nat_even hk
      rw [if_pos hk] at ih
      have hodd : ¬ Even (k + 1) := by simp [Nat.even_add_one, hk]
      rw [show k + 1 + 1 = k + 2 from rfl, show k + 1 + 2 = k + 3 from rfl, if_neg hodd]
      omega
    · -- k odd, so k+1 is even
      have hc := gap_nat_odd hk
      rw [if_neg (by simpa [Nat.not_even_iff_odd] using hk)] at ih
      have heven : Even (k + 1) := hk.add_one
      rw [show k + 1 + 1 = k + 2 from rfl, show k + 1 + 2 = k + 3 from rfl, if_pos heven]
      omega

/-- Even branch: `F₀F₂ + ⋯ + FₙFₙ₊₂ = Fₙ₊₁Fₙ₊₂ − 1` when `n` is even. -/
theorem fib_gap_two_even {n : ℕ} (hn : Even n) :
    (∑ i ∈ Finset.range (n + 1), Nat.fib i * Nat.fib (i + 2))
      = Nat.fib (n + 1) * Nat.fib (n + 2) - 1 := by
  have h := fib_gap_two_prod_sum n
  rw [if_pos hn] at h
  omega

/-- Odd branch: `F₀F₂ + ⋯ + FₙFₙ₊₂ = Fₙ₊₁Fₙ₊₂` when `n` is odd. -/
theorem fib_gap_two_odd {n : ℕ} (hn : Odd n) :
    (∑ i ∈ Finset.range (n + 1), Nat.fib i * Nat.fib (i + 2))
      = Nat.fib (n + 1) * Nat.fib (n + 2) := by
  have h := fib_gap_two_prod_sum n
  rw [if_neg (by simpa [Nat.not_even_iff_odd] using hn)] at h
  omega

end FibonacciIdentitiesOQ05OQ03
