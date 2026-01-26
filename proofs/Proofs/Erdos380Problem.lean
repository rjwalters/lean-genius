/-!
# Erdős Problem 380: Bad Intervals and Greatest Prime Factors

An interval `[u, v]` is "bad" if the greatest prime factor of `∏{u ≤ m ≤ v} m`
occurs with exponent > 1 in the product. Let `B(x)` count integers `n ≤ x`
contained in at least one bad interval.

**Conjecture:** `B(x) ~ #{n ≤ x : P(n)² | n}` where `P(n)` is the
greatest prime factor of `n`.

Erdős and Graham (1980) proved `B(x) > x^{1-o(1)}`.

*Reference:* [erdosproblems.com/380](https://www.erdosproblems.com/380)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! ## Greatest prime factor -/

/-- The greatest prime factor of `n`. Returns 0 for `n ≤ 1`. -/
axiom greatestPrimeFactor : ℕ → ℕ

/-- `greatestPrimeFactor n` is prime for `n ≥ 2`. -/
axiom gpf_prime (n : ℕ) (hn : 2 ≤ n) :
    (greatestPrimeFactor n).Prime

/-- `greatestPrimeFactor n` divides `n`. -/
axiom gpf_dvd (n : ℕ) (hn : 2 ≤ n) :
    greatestPrimeFactor n ∣ n

/-- `greatestPrimeFactor n` is the largest prime dividing `n`. -/
axiom gpf_largest (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hd : p ∣ n) :
    p ≤ greatestPrimeFactor n

/-! ## Bad intervals -/

/-- An interval `[u, v]` is bad if the greatest prime factor of the
product `u * (u+1) * ⋯ * v` occurs with exponent ≥ 2. -/
def IsBadInterval (u v : ℕ) : Prop :=
    u ≤ v ∧
    let P := greatestPrimeFactor (Finset.Icc u v).prod id
    P ^ 2 ∣ (Finset.Icc u v).prod id

/-- An integer `n` is in a bad interval if there exist `u ≤ n ≤ v`
with `[u, v]` bad. -/
def InBadInterval (n : ℕ) : Prop :=
    ∃ (u v : ℕ), u ≤ n ∧ n ≤ v ∧ IsBadInterval u v

/-! ## Counting functions -/

/-- `B(x)`: count of integers `n ≤ x` in some bad interval. -/
noncomputable def badCount (x : ℕ) : ℕ :=
    ((Finset.Icc 1 x).filter InBadInterval).card

/-- Count of `n ≤ x` with `P(n)² | n`. -/
noncomputable def gpfSquareCount (x : ℕ) : ℕ :=
    ((Finset.Icc 2 x).filter
      (fun n => greatestPrimeFactor n ^ 2 ∣ n)).card

/-! ## Main conjecture -/

/-- Erdős Problem 380: `B(x) ~ #{n ≤ x : P(n)² | n}`.
Formally: the ratio tends to 1. -/
def ErdosProblem380 : Prop :=
    ∀ (ε : ℚ), 0 < ε →
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        0 < gpfSquareCount x ∧
          |(badCount x : ℚ) / (gpfSquareCount x : ℚ) - 1| < ε

/-! ## Known bounds -/

/-- Erdős–Graham: `B(x) > x^{1-o(1)}`, meaning `B(x)` is large. -/
axiom erdos_graham_lower :
    ∀ (ε : ℚ), 0 < ε →
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (x : ℚ) ^ (1 - ε) ≤ (badCount x : ℚ)

/-- The count `#{n ≤ x : P(n)² | n}` grows like
`x / exp(c √(log x · log log x))` for some `c > 0`. -/
axiom gpfSquare_asymptotic :
    ∃ c : ℚ, 0 < c ∧
      ∀ (ε : ℚ), 0 < ε →
        ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
          (x : ℚ) ^ (1 - ε) ≤ (gpfSquareCount x : ℚ)

/-! ## Bad intervals and primes -/

/-- Bad intervals cannot contain primes (since a prime `p` in `[u,v]`
would make `p` the greatest prime factor, appearing exactly once in
the product if `v < 2p`). -/
axiom bad_interval_no_prime (u v : ℕ) (hbad : IsBadInterval u v) :
    v < 2 * u →
      ∀ p : ℕ, p.Prime → u ≤ p → p ≤ v → False
