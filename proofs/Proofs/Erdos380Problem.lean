/-
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
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

open Nat Finset

/- ## Greatest prime factor

Previously axiomatized (4 axioms: definition + 3 properties).
Now defined concretely via `Nat.primeFactors` and `Finset.max'`,
with all properties proved from the definition. -/

/-- The greatest prime factor of `n`. Returns 0 for `n ≤ 1`.
    Defined as the maximum of the prime factor set.
    Previously an axiom; now concrete via Mathlib. -/
noncomputable def greatestPrimeFactor (n : ℕ) : ℕ :=
  if h : n > 1 then n.primeFactors.max' (Nat.primeFactors_nonempty h) else 0

/-- `greatestPrimeFactor n` is prime for `n ≥ 2`.
    Previously axiomatized; now proved from the definition. -/
theorem gpf_prime (n : ℕ) (hn : 2 ≤ n) :
    (greatestPrimeFactor n).Prime := by
  unfold greatestPrimeFactor
  rw [dif_pos (by omega : n > 1)]
  have hmem := Finset.max'_mem n.primeFactors (Nat.primeFactors_nonempty (by omega : n > 1))
  exact (Nat.mem_primeFactors.mp hmem).1

/-- `greatestPrimeFactor n` divides `n`.
    Previously axiomatized; now proved from the definition. -/
theorem gpf_dvd (n : ℕ) (hn : 2 ≤ n) :
    greatestPrimeFactor n ∣ n := by
  unfold greatestPrimeFactor
  rw [dif_pos (by omega : n > 1)]
  have hmem := Finset.max'_mem n.primeFactors (Nat.primeFactors_nonempty (by omega : n > 1))
  exact (Nat.mem_primeFactors.mp hmem).2.1

/-- `greatestPrimeFactor n` is the largest prime dividing `n`.
    Previously axiomatized; now proved from the definition. -/
theorem gpf_largest (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hd : p ∣ n) :
    p ≤ greatestPrimeFactor n := by
  unfold greatestPrimeFactor
  rw [dif_pos (by omega : n > 1)]
  apply Finset.le_max'
  exact Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩

/- ## Bad intervals -/

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

/- ## Counting functions -/

/-- `B(x)`: count of integers `n ≤ x` in some bad interval. -/
noncomputable def badCount (x : ℕ) : ℕ :=
    ((Finset.Icc 1 x).filter InBadInterval).card

/-- Count of `n ≤ x` with `P(n)² | n`. -/
noncomputable def gpfSquareCount (x : ℕ) : ℕ :=
    ((Finset.Icc 2 x).filter
      (fun n => greatestPrimeFactor n ^ 2 ∣ n)).card

/- ## Main conjecture -/

/-- Erdős Problem 380: `B(x) ~ #{n ≤ x : P(n)² | n}`.
Formally: the ratio tends to 1. -/
def ErdosProblem380 : Prop :=
    ∀ (ε : ℚ), 0 < ε →
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        0 < gpfSquareCount x ∧
          |(badCount x : ℚ) / (gpfSquareCount x : ℚ) - 1| < ε

/- ## Known bounds -/

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

/- ## Bad intervals and primes -/

/-- Bad intervals with `v < 2u` cannot contain primes. If `p` is prime
and `p ∈ [u,v]` with `v < 2u`, then `p` is the only multiple of itself
in the interval, so it appears with exponent 1 in the product — contradicting
the "bad" condition that requires the greatest prime factor to have exponent ≥ 2. -/
axiom bad_interval_no_prime (u v : ℕ) (hbad : IsBadInterval u v) :
    v < 2 * u →
      ∀ p : ℕ, p.Prime → u ≤ p → p ≤ v → False
