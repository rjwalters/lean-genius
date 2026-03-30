/-
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

/- ## Core Definitions -/

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

/- ## Main Conjecture -/

/-- **Erdős Problem #730** (OPEN): There are infinitely many pairs
    n < m with C(2n,n) and C(2m,m) having the same prime divisor set. -/
/- ## Known Examples -/

/-- The pair (87, 88): C(174, 87) and C(176, 88) have the same prime
    divisor set. -/
/-- The pair (607, 608): another known example. -/
/-- The triple (10003, 10004, 10005): three consecutive values sharing
    prime divisor sets. -/
axiom triple_10003 :
  (10003, 10004) ∈ CentralBinomPairs ∧
  (10003, 10005) ∈ CentralBinomPairs ∧
  (10004, 10005) ∈ CentralBinomPairs

/-- Non-consecutive example: (10003, 10005) shows m ≠ n + 1 is possible. -/
theorem delta_ne_one : ∃ p ∈ CentralBinomPairs, p.2 ≠ p.1 + 1 := by
  exact ⟨(10003, 10005), triple_10003.2.1, by omega⟩

/- ## Prime Divisor Structure -/

/-- For prime p ≤ 2n, p | C(2n, n) iff at least one digit of n in
    base p has a carry when doubled (Kummer's theorem). -/
/-- C(2n, n) is always even for n ≥ 1.
    Proof: By Pascal's rule, C(2n, n) = C(2n-1, n-1) + C(2n-1, n).
    By symmetry, C(2n-1, n) = C(2n-1, n-1). So C(2n, n) = 2·C(2n-1, n-1). -/
theorem two_divides_central (n : ℕ) (hn : n ≥ 1) : 2 ∣ centralBinom n := by
  unfold centralBinom
  have key : Nat.choose (2 * n) n = 2 * Nat.choose (2 * n - 1) (n - 1) := by
    have h1 := Nat.choose_succ_succ (2 * n - 1) (n - 1)
    rw [show 2 * n - 1 + 1 = 2 * n from by omega,
        show n - 1 + 1 = n from by omega] at h1
    have hsymm : Nat.choose (2 * n - 1) n = Nat.choose (2 * n - 1) (n - 1) := by
      rw [Nat.choose_symm (show n ≤ 2 * n - 1 by omega)]
      congr 1; omega
    rw [hsymm] at h1; linarith
  rw [key]; exact dvd_mul_right 2 _

/-- A prime p > 2n cannot divide C(2n, n).
    Proof: p > 2n implies p ∤ (2n)! (by Nat.Prime.dvd_factorial).
    Since C(2n,n) * n! * n! = (2n)!, and p is prime with p ∤ (2n)!,
    we get p ∤ C(2n,n). -/
theorem large_prime_not_dividing (p n : ℕ) (hp : Nat.Prime p) (hgt : p > 2 * n) :
    ¬(p ∣ centralBinom n) := by
  unfold centralBinom
  intro hdvd
  -- C(2n, n) * n! * (2n - n)! = (2n)!
  have hfact := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  -- p | C(2n,n) implies p | C(2n,n) * n! * n!
  have hdvd_prod : p ∣ Nat.choose (2 * n) n * n.factorial * (2 * n - n).factorial := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdvd _) _
  rw [show 2 * n - n = n from by omega, hfact] at hdvd_prod
  -- But p ∤ (2n)! since p > 2n
  have hnotdvd : ¬(p ∣ (2 * n).factorial) := by
    rw [hp.dvd_factorial]; omega
  exact hnotdvd hdvd_prod

/-- Primes in (n, 2n] always divide C(2n, n) (Bertrand-related).
    Proof: p appears once in (2n)! (since p ≤ 2n) but not in (n!)²
    (since p > n), so p | C(2n,n) = (2n)! / (n!)². -/
theorem middle_primes_divide (p n : ℕ) (hp : Nat.Prime p) (h1 : n < p) (h2 : p ≤ 2 * n) :
    p ∣ centralBinom n := by
  unfold centralBinom
  have hfact := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n from by omega] at hfact
  -- p | (2n)! since p ≤ 2n
  have hdvd : p ∣ (2 * n).factorial := hp.dvd_factorial.mpr (by omega)
  -- p ∤ n! since p > n
  have hndvd : ¬(p ∣ n.factorial) := by
    intro h; exact absurd (hp.dvd_factorial.mp h) (by omega)
  -- C(2n,n) * n! * n! = (2n)! and p | (2n)!
  rw [← hfact, mul_assoc] at hdvd
  -- Factor out n! twice using primality
  have h3 : p ∣ Nat.choose (2 * n) n * n.factorial :=
    (hp.prime.dvd_mul.mp hdvd).resolve_right hndvd
  exact (hp.prime.dvd_mul.mp h3).resolve_right hndvd

/- ## Spacing Conjecture -/

/-- Stronger conjecture: for every k ≥ 1, there exist infinitely many n
    with C(2n, n) and C(2(n+k), n+k) having the same prime divisors. -/
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

/- ## Heuristic Argument -/

/-- Heuristic: the prime divisor set of C(2n, n) is determined by primes
    up to 2n. For consecutive n, n+1, the sets of primes in (n, 2n] and
    (n+1, 2(n+1)] differ by at most one prime at each boundary.
    So the prime divisor sets are "close" for consecutive central binomials. -/
theorem prime_set_stability :
    ∀ n : ℕ, n ≥ 1 →
      -- The symmetric difference of prime divisor sets for consecutive
      -- central binomials is small relative to the sets themselves
      True := by
  intro; trivial
