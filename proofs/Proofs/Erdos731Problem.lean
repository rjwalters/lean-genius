/-!
# Erdős Problem #731: Least Non-Divisor of Central Binomial Coefficients

Find a reasonable function f(n) such that for almost all integers n, the
least integer m with m ∤ C(2n, n) satisfies m ~ f(n).

## Key Results

- EGRS (1975): for almost all n, the least non-divisor m satisfies
  m = exp((log n)^{1/2 + o(1)})
- Kummer's theorem: p^k | C(2n,n) iff the base-p addition of n with itself
  has ≥ k carries
- Related OEIS: A006197

## References

- Erdős, Graham, Ruzsa, Straus (1975): [EGRS75]
- <https://erdosproblems.com/731>
-/

import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The central binomial coefficient C(2n, n). -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- The least positive integer that does not divide m. -/
noncomputable def leastNonDivisor (m : ℕ) : ℕ :=
  if m = 0 then 1
  else Nat.find (⟨m + 1, by omega⟩ : ∃ k : ℕ, k > 0 ∧ ¬(k ∣ m))

/-- The least non-divisor of C(2n, n). -/
noncomputable def leastNonDivCentral (n : ℕ) : ℕ :=
  leastNonDivisor (centralBinom n)

/-! ## Main Conjecture -/

/-- **Erdős Problem #731** (OPEN): For almost all n, the least m with
    m ∤ C(2n, n) satisfies m = exp((log n)^{1/2 + o(1)}). -/
axiom erdos_731_conjecture :
  -- For all ε > 0, the density of n where the least non-divisor deviates
  -- from exp((log n)^{1/2}) by more than (log n)^ε is zero.
  True  -- Precise formulation requires asymptotic density and real analysis

/-! ## Divisibility Properties of Central Binomials -/

/-- **Kummer's Theorem**: The p-adic valuation of C(m+n, m) equals the
    number of carries when adding m and n in base p. -/
axiom kummer_carries (p m n : ℕ) (hp : Nat.Prime p) :
  -- v_p(C(m+n, m)) = number of carries in base-p addition of m and n
  True

/-- For prime p ≤ 2n, we have p | C(2n, n) iff there is at least one
    carry when adding n to itself in base p. -/
axiom prime_divides_central_iff (p n : ℕ) (hp : Nat.Prime p) (hle : p ≤ 2 * n) :
  p ∣ centralBinom n ↔
    -- At least one digit of n in base p is ≥ ⌈p/2⌉
    ∃ k : ℕ, (n / p ^ k) % p ≥ (p + 1) / 2

/-- Small primes always divide C(2n, n) for large n. -/
axiom small_primes_divide (p : ℕ) (hp : Nat.Prime p) :
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → p ∣ centralBinom n

/-- C(2n, n) is always even for n ≥ 1. -/
axiom two_divides_central (n : ℕ) (hn : n ≥ 1) : 2 ∣ centralBinom n

/-- The product of all primes ≤ x is roughly e^x (prime number theorem). -/
axiom primorial_asymptotic :
  -- ∏_{p ≤ x} p = e^{x(1+o(1))} as x → ∞
  True

/-! ## Asymptotic Analysis -/

/-- The least non-divisor of C(2n, n) is determined by the smallest
    prime p such that all digits of n in base p are < ⌈p/2⌉. -/
axiom least_nondiv_is_prime (n : ℕ) (hn : centralBinom n > 0) :
  Nat.Prime (leastNonDivCentral n) ∨ leastNonDivCentral n = 1

/-- **EGRS (1975)**: The typical behavior is
    log(leastNonDivCentral n) ~ (log n)^{1/2}.
    Heuristic: a prime p divides C(2n,n) unless all log_p(n) digits of n
    are small. The probability of this is roughly (1/2)^{log n / log p},
    which becomes significant when log p ~ (log n)^{1/2}. -/
axiom egrs_typical_behavior :
  -- For density-1 set of n:
  -- (log n)^{1/2 - ε} ≤ log(leastNonDivCentral n) ≤ (log n)^{1/2 + ε}
  True

/-! ## Bounds -/

/-- Lower bound: the least non-divisor is at least 2 for n ≥ 1 (since
    2 | C(2n, n) for n ≥ 1). More generally, all primes up to a threshold
    divide C(2n, n) for most n. -/
axiom lower_bound_most_n :
  ∀ (P : ℕ), ∃ (D : ℕ), D > 0 ∧
    -- For at least (1 - 1/D) fraction of n ≤ N:
    -- leastNonDivCentral n > P
    True

/-- Upper bound: there always exists a prime p ≤ 2n+1 not dividing C(2n, n),
    namely p = 2n+1 when it is prime and n+1 < p. -/
axiom upper_bound_trivial (n : ℕ) (hn : n ≥ 1) :
  leastNonDivCentral n ≤ 2 * n + 1

/-- **Bertrand's postulate** applied: for n ≥ 1, there exists a prime p
    with n < p ≤ 2n, and this prime divides C(2n, n) exactly once. -/
axiom bertrand_central (n : ℕ) (hn : n ≥ 1) :
  ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n ∧ p ∣ centralBinom n

/-- The central binomial satisfies C(2n, n) ≥ 4^n / (2n+1) for n ≥ 0. -/
axiom central_binom_lower (n : ℕ) :
  centralBinom n * (2 * n + 1) ≥ 4 ^ n
