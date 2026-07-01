import Mathlib

/-
# Fibonacci primes force (almost) prime indices

The parent entry `FibonacciIdentitiesOQ02` establishes that the Fibonacci
numbers are a *strong divisibility sequence*: `fib (gcd m n) = gcd (fib m) (fib n)`,
with the sharp characterization `fib m ∣ fib n ↔ m ∣ n` for `3 ≤ m`.

A classical consequence of index-divisibility is a constraint on which indices
can produce *prime* Fibonacci numbers:

  **If `fib n` is prime, then `n` is prime or `n = 4`.**

The exceptional index `n = 4` is genuine: `fib 4 = 3` is prime while `4` is not.
It is the unique composite index that escapes, because `4`'s only proper divisor
above `1` is `2`, and `fib 2 = 1` is a unit.

The proof is a clean application of the divisibility law. If `n` is composite and
`n ≠ 4`, then `n` has a divisor `d` with `3 ≤ d < n`; then `fib d ∣ fib n`
(`Nat.fib_dvd`), `2 ≤ fib d` (monotonicity, `fib 3 = 2`), and `fib d < fib n`
(strict monotonicity, `Nat.fib_lt_fib`, since `d < n`). So `fib n` has a divisor
strictly between `1` and itself, hence is not prime.

The converse is false: `19` is prime but `fib 19 = 4181 = 37 · 113` is composite,
so prime indices do **not** force prime Fibonacci numbers. This one-directional
result is exactly what the strong-divisibility structure buys.

No axioms, no `sorry`, no `native_decide`.

Parent: FibonacciIdentitiesOQ02.lean
-/

namespace FibonacciIdentitiesOQ02OQ02PrimeIndex

open Nat

/-- A composite number other than `4` always has a divisor in the range `[3, n)`.
This is the combinatorial core: it isolates a nontrivial index divisor whose
Fibonacci value is a proper (`> 1`) divisor of `fib n`. The special role of `4`
is exactly that its only proper divisor above `1` is `2`, which lands in the
degenerate `fib 2 = 1` regime. -/
theorem exists_divisor_ge_three {n : ℕ} (hn : 2 ≤ n) (hnp : ¬ n.Prime)
    (hn4 : n ≠ 4) : ∃ d, d ∣ n ∧ 3 ≤ d ∧ d < n := by
  obtain ⟨m, hm_dvd, hm2, hmn⟩ := Nat.exists_dvd_of_not_prime2 hn hnp
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · -- `2 ≤ m < 3` forces `m = 2`, so `n` is even; use the cofactor `n / 2`.
    have hm : m = 2 := by omega
    subst hm
    obtain ⟨k, hk⟩ := hm_dvd          -- `n = 2 * k`
    exact ⟨k, ⟨2, by rw [hk]; ring⟩, by omega, by omega⟩
  · exact ⟨m, hm_dvd, hm3, hmn⟩

/-- **Main result**: a prime Fibonacci number has a prime or `4` index.
If `fib n` is prime then `n` is prime or `n = 4`. -/
theorem fib_prime_imp_index_prime_or_four {n : ℕ}
    (hp : (Nat.fib n).Prime) : n.Prime ∨ n = 4 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnp, hn4⟩ := hcon
  -- `fib n` prime ⇒ `fib n ≥ 2` ⇒ `n ≥ 3` (since `fib 0,1,2 ∈ {0,1}`).
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with h | h
    · exact absurd hp (by interval_cases n <;> decide)
    · exact h
  -- Extract a nontrivial index divisor `3 ≤ d < n`.
  obtain ⟨d, hd_dvd, hd3, hdn⟩ := exists_divisor_ge_three (by omega) hnp hn4
  -- Its Fibonacci value is a proper divisor of `fib n`.
  have hfd : Nat.fib d ∣ Nat.fib n := Nat.fib_dvd d n hd_dvd
  have h2 : 2 ≤ Nat.fib d := by
    have : Nat.fib 3 ≤ Nat.fib d := Nat.fib_mono hd3
    simpa using this
  have hlt : Nat.fib d < Nat.fib n := (Nat.fib_lt_fib (by omega : 2 ≤ d)).mpr hdn
  -- A prime cannot have a divisor strictly between `1` and itself.
  rcases hp.eq_one_or_self_of_dvd (Nat.fib d) hfd with h1 | hself
  · omega
  · omega

/-- For indices `n ≥ 5`, a prime Fibonacci number forces a prime index outright
(the `n = 4` exception only matters below `5`). -/
theorem fib_prime_index_prime_of_ge_five {n : ℕ} (hn : 5 ≤ n)
    (hp : (Nat.fib n).Prime) : n.Prime := by
  rcases fib_prime_imp_index_prime_or_four hp with h | h
  · exact h
  · omega

/-- Contrapositive form: a composite index other than `4` yields a composite
Fibonacci number. -/
theorem fib_not_prime_of_composite {n : ℕ} (hnp : ¬ n.Prime) (hn4 : n ≠ 4) :
    ¬ (Nat.fib n).Prime := by
  intro hp
  rcases fib_prime_imp_index_prime_or_four hp with h | h
  · exact hnp h
  · exact hn4 h

-- ═══════════════════════════════════════════════════════════════════
-- Sharpness and one-directionality
-- ═══════════════════════════════════════════════════════════════════

/-- The exceptional index `n = 4` is real: `fib 4 = 3` is prime while `4` is not.
This is why the conclusion is `n.Prime ∨ n = 4` and not simply `n.Prime`. -/
example : (Nat.fib 4).Prime ∧ ¬ Nat.Prime 4 := by decide

/-- `n = 4` is the *only* composite escaping index: for every other composite
index the theorem already forbids a prime value; `fib 4 = 3` shows the escape
is nonempty and pinned to `4`. -/
example : Nat.fib 4 = 3 := by decide

/-- The converse fails. `19` is prime, yet `fib 19 = 4181 = 37 · 113` is composite:
prime indices do not force prime Fibonacci numbers. The implication is strictly
one-directional. -/
example : Nat.Prime 19 ∧ ¬ (Nat.fib 19).Prime := by
  refine ⟨by decide, ?_⟩
  rw [show Nat.fib 19 = 4181 from by decide]
  -- 4181 = 37 * 113
  intro h
  have := h.eq_one_or_self_of_dvd 37 (by norm_num)
  omega

end FibonacciIdentitiesOQ02OQ02PrimeIndex
