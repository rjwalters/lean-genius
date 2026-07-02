import Proofs.FibonacciIdentitiesOQ02OQ01OQ01
import Mathlib.Tactic

/-
# The Exact `gcd(Fₙ, Lₙ)`: `2 ⟺ 3 ∣ n`, and `1` otherwise

## Open Question OQ-02-OQ-01-OQ-01-OQ-01

The parent entry (`fibonacci-identities-oq-02-oq-01-oq-01`) proved the
Fibonacci–Lucas quadratic identity `Lₙ² − 5·Fₙ² = 4·(−1)ⁿ` and used it to pin
the same-index interaction down to a *factor of two*:

    gcd(Fₙ, Lₙ) ∣ 2        so   gcd(Fₙ, Lₙ) ∈ {1, 2}.

The parent left **which** of the two values occurs as an open question. This
entry settles it as a universally quantified biconditional:

    gcd(Fₙ, Lₙ) = 2   ⟺   3 ∣ n                    (`gcd_fib_lucas_eq_two_iff`)
    gcd(Fₙ, Lₙ) = 1   ⟺   ¬ 3 ∣ n                  (`gcd_fib_lucas_eq_one_iff`)
    gcd(Fₙ, Lₙ) = if 3 ∣ n then 2 else 1           (`gcd_fib_lucas`)

## How It's Proved

Since `gcd(Fₙ, Lₙ) ∈ {1, 2}`, the value is `2` **exactly when the gcd is even**,
i.e. exactly when *both* `Fₙ` and `Lₙ` are even. So the whole question collapses
to a **parity** computation, and the two sequences share the *same* parity:

* **`2 ∣ Fₙ ⟺ 3 ∣ n`** (`fib_even_iff`). The parity of the Fibonacci sequence
  is `3`-periodic — `0,1,1,0,1,1,…` — because
  `Fₙ₊₃ = Fₙ + 2·Fₙ₊₁ ≡ Fₙ (mod 2)` (`fib_add_three`). A three-residue
  induction closes the biconditional.

* **`2 ∣ Lₙ ⟺ 2 ∣ Fₙ`** (`lucas_even_iff_fib_even`). Immediate from the
  parent's subtraction-free bridge `2·Fₙ₊₁ = Lₙ + Fₙ`: modulo `2` this says
  `Lₙ ≡ −Fₙ ≡ Fₙ`, so the companion sequences have identical parity.

Combining, `Lₙ` is even `⟺ 3 ∣ n` as well, so both are even together precisely
on the multiples of `3`, which is exactly where the gcd hits `2`.
-/

namespace FibonacciIdentitiesOQ02OQ01OQ01OQ01

open Nat FibonacciIdentitiesOQ02OQ01OQ01

/-! ## Fibonacci parity is `3`-periodic -/

/-- The parity-carrying step `Fₙ₊₃ = Fₙ + 2·Fₙ₊₁`. Modulo `2` this is
`Fₙ₊₃ ≡ Fₙ`, the engine of the `3`-periodicity of Fibonacci parity. -/
theorem fib_add_three (n : ℕ) : fib (n + 3) = fib n + 2 * fib (n + 1) := by
  have h1 : fib (n + 3) = fib (n + 1) + fib (n + 2) := fib_add_two
  have h2 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
  omega

/-- **Fibonacci parity criterion:** `Fₙ` is even iff `3 ∣ n`. The parity
sequence `0,1,1,0,1,1,…` has period `3`; proved by induction over the three
residues using `Fₙ₊₃ ≡ Fₙ (mod 2)`. -/
theorem fib_even_iff : ∀ n, (2 ∣ fib n ↔ 3 ∣ n)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | (n + 3) => by
      have hper : fib (n + 3) = fib n + 2 * fib (n + 1) := fib_add_three n
      have ih := fib_even_iff n
      have h3 : (3 ∣ n + 3) ↔ 3 ∣ n := by omega
      rw [hper, h3, ← ih]
      constructor <;> intro h <;> omega

/-! ## Lucas and Fibonacci share their parity -/

/-- **`2 ∣ Lₙ ⟺ 2 ∣ Fₙ`.** The companion sequences have identical parity,
directly from the parent's bridge `2·Fₙ₊₁ = Lₙ + Fₙ`. -/
theorem lucas_even_iff_fib_even (n : ℕ) : 2 ∣ lucas n ↔ 2 ∣ fib n := by
  have h := two_mul_fib_succ n
  omega

/-- **Lucas parity criterion:** `Lₙ` is even iff `3 ∣ n`. -/
theorem lucas_even_iff (n : ℕ) : 2 ∣ lucas n ↔ 3 ∣ n := by
  rw [lucas_even_iff_fib_even]; exact fib_even_iff n

/-! ## The exact gcd value -/

/-- **`gcd(Fₙ, Lₙ) = 2 ⟺ 3 ∣ n`.** The factor `2` in the parent's bound
`gcd(Fₙ, Lₙ) ∣ 2` is attained *exactly* on the multiples of `3`. -/
theorem gcd_fib_lucas_eq_two_iff (n : ℕ) :
    Nat.gcd (fib n) (lucas n) = 2 ↔ 3 ∣ n := by
  constructor
  · intro h
    have hdf : (2 : ℕ) ∣ fib n := by
      rw [← h]; exact Nat.gcd_dvd_left (fib n) (lucas n)
    exact (fib_even_iff n).mp hdf
  · intro h
    have hf : 2 ∣ fib n := (fib_even_iff n).mpr h
    have hl : 2 ∣ lucas n := (lucas_even_iff n).mpr h
    have hg2 : 2 ∣ Nat.gcd (fib n) (lucas n) := Nat.dvd_gcd hf hl
    rcases gcd_fib_lucas_eq_one_or_two n with h1 | h2
    · rw [h1] at hg2; exact absurd hg2 (by decide)
    · exact h2

/-- **`gcd(Fₙ, Lₙ) = 1 ⟺ ¬ 3 ∣ n`.** The coprime case is exactly the
non-multiples of `3`. -/
theorem gcd_fib_lucas_eq_one_iff (n : ℕ) :
    Nat.gcd (fib n) (lucas n) = 1 ↔ ¬ 3 ∣ n := by
  constructor
  · intro h1 hdvd
    have h2 : Nat.gcd (fib n) (lucas n) = 2 := (gcd_fib_lucas_eq_two_iff n).mpr hdvd
    omega
  · intro h
    rcases gcd_fib_lucas_eq_one_or_two n with h1 | h2
    · exact h1
    · exact absurd ((gcd_fib_lucas_eq_two_iff n).mp h2) h

/-- **The exact gcd, in closed form:** `gcd(Fₙ, Lₙ) = if 3 ∣ n then 2 else 1`.
This is the full answer to the parent's open question. -/
theorem gcd_fib_lucas (n : ℕ) :
    Nat.gcd (fib n) (lucas n) = if 3 ∣ n then 2 else 1 := by
  by_cases h : 3 ∣ n
  · rw [if_pos h]; exact (gcd_fib_lucas_eq_two_iff n).mpr h
  · rw [if_neg h]; exact (gcd_fib_lucas_eq_one_iff n).mpr h

/-! ## Concrete sanity checks -/

/-- `gcd(F₆, L₆) = gcd(8, 18) = 2`, and `3 ∣ 6`. -/
theorem check_six : Nat.gcd (fib 6) (lucas 6) = 2 := by decide

/-- `gcd(F₉, L₉) = gcd(34, 76) = 2`, and `3 ∣ 9`. -/
theorem check_nine : Nat.gcd (fib 9) (lucas 9) = 2 := by decide

/-- `gcd(F₅, L₅) = gcd(5, 11) = 1`, and `¬ 3 ∣ 5`. -/
theorem check_five : Nat.gcd (fib 5) (lucas 5) = 1 := by decide

/-- `gcd(F₇, L₇) = gcd(13, 29) = 1`, and `¬ 3 ∣ 7`. -/
theorem check_seven : Nat.gcd (fib 7) (lucas 7) = 1 := by decide

end FibonacciIdentitiesOQ02OQ01OQ01OQ01
