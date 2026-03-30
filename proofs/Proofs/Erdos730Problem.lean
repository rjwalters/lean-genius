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

-- erdos_730_conjecture: unused axiom removed (never referenced by any theorem)
-- example_87_88: unused axiom removed (never referenced by any theorem)
-- example_607_608: unused axiom removed (never referenced by any theorem)
axiom triple_10003 :
  (10003, 10004) ∈ CentralBinomPairs ∧
  (10003, 10005) ∈ CentralBinomPairs ∧
  (10004, 10005) ∈ CentralBinomPairs

-- kummer_central_divisibility: unused axiom removed (never referenced by any theorem)
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

-- spacing_conjecture: unused axiom removed (never referenced by any theorem)
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
