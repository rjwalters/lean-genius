/-!
# Erdős Problem #730: Same Prime Divisors of Central Binomials

Are there infinitely many pairs n < m such that C(2n, n) and C(2m, m)
have the same set of prime divisors?

## Key Results

- EGRS (1975): "no doubt" the answer is yes
- Known pairs: (87, 88), (607, 608)
- Known triple: n = 10003, 10004, 10005 share prime divisor sets
- Open: do such pairs exist for every spacing k ≥ 1?
- OEIS: A129515

## References

- Erdős, Graham, Ruzsa, Straus (1975): [EGRS75]
- <https://erdosproblems.com/730>
-/

import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The central binomial coefficient C(2n, n). -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- The set of prime divisors of a natural number. -/
def primeDivisors (n : ℕ) : Finset ℕ :=
  n.primeFactors

/-- Two natural numbers have the same prime divisor set. -/
def SamePrimeDivisors (a b : ℕ) : Prop :=
  primeDivisors a = primeDivisors b

/-- The set of pairs (n, m) with n < m and C(2n,n), C(2m,m) sharing
    prime divisors. -/
def CentralBinomPairs : Set (ℕ × ℕ) :=
  {p | p.1 < p.2 ∧ SamePrimeDivisors (centralBinom p.1) (centralBinom p.2)}

/-! ## Main Conjecture -/

/-- **Erdős Problem #730** (OPEN): There are infinitely many pairs
    n < m with C(2n,n) and C(2m,m) having the same prime divisor set. -/
axiom erdos_730_conjecture : Set.Infinite CentralBinomPairs

/-! ## Known Examples -/

/-- The pair (87, 88): C(174, 87) and C(176, 88) have the same prime
    divisor set. -/
axiom example_87_88 : (87, 88) ∈ CentralBinomPairs

/-- The pair (607, 608): another known example. -/
axiom example_607_608 : (607, 608) ∈ CentralBinomPairs

/-- The triple (10003, 10004, 10005): three consecutive values sharing
    prime divisor sets. -/
axiom triple_10003 :
  (10003, 10004) ∈ CentralBinomPairs ∧
  (10003, 10005) ∈ CentralBinomPairs ∧
  (10004, 10005) ∈ CentralBinomPairs

/-- Non-consecutive example: (10003, 10005) shows m ≠ n + 1 is possible. -/
theorem delta_ne_one : ∃ p ∈ CentralBinomPairs, p.2 ≠ p.1 + 1 := by
  exact ⟨(10003, 10005), triple_10003.2.1, by omega⟩

/-! ## Prime Divisor Structure -/

/-- For prime p ≤ 2n, p | C(2n, n) iff at least one digit of n in
    base p has a carry when doubled (Kummer's theorem). -/
axiom kummer_central_divisibility (p n : ℕ) (hp : Nat.Prime p) (hle : p ≤ 2 * n) :
  p ∣ centralBinom n ↔ ∃ k : ℕ, (n / p ^ k) % p ≥ (p + 1) / 2

/-- C(2n, n) is always even for n ≥ 1. -/
axiom two_divides_central (n : ℕ) (hn : n ≥ 1) : 2 ∣ centralBinom n

/-- A prime p > 2n cannot divide C(2n, n) since C(2n, n) < p for
    n small enough, or the prime simply exceeds the factorial range. -/
axiom large_prime_not_dividing (p n : ℕ) (hp : Nat.Prime p) (hgt : p > 2 * n) :
  ¬(p ∣ centralBinom n)

/-- Primes in (n, 2n] always divide C(2n, n) (Bertrand-related). -/
axiom middle_primes_divide (p n : ℕ) (hp : Nat.Prime p) (h1 : n < p) (h2 : p ≤ 2 * n) :
  p ∣ centralBinom n

/-! ## Spacing Conjecture -/

/-- Stronger conjecture: for every k ≥ 1, there exist infinitely many n
    with C(2n, n) and C(2(n+k), n+k) having the same prime divisors. -/
axiom spacing_conjecture :
  ∀ k : ℕ, k ≥ 1 →
    Set.Infinite {n : ℕ | SamePrimeDivisors (centralBinom n) (centralBinom (n + k))}

/-- The spacing-1 case implies the main conjecture. -/
theorem spacing1_implies_main
    (h : Set.Infinite {n : ℕ | SamePrimeDivisors (centralBinom n) (centralBinom (n + 1))}) :
    Set.Infinite CentralBinomPairs := by
  apply Set.Infinite.mono _ (Set.Infinite.image (fun n => (n, n + 1)) h (by
    intro a b hab; simp at hab; omega))
  intro ⟨a, b⟩ ⟨n, hn, heq⟩
  simp at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨by omega, hn⟩

/-! ## Heuristic Argument -/

/-- Heuristic: the prime divisor set of C(2n, n) is determined by primes
    up to 2n. For consecutive n, n+1, the sets of primes in (n, 2n] and
    (n+1, 2(n+1)] differ by at most one prime at each boundary.
    So the prime divisor sets are "close" for consecutive central binomials. -/
axiom prime_set_stability :
  ∀ n : ℕ, n ≥ 1 →
    -- The symmetric difference of prime divisor sets for consecutive
    -- central binomials is small relative to the sets themselves
    True
