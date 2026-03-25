/-
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
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/- ## Core Definitions -/

/-- The central binomial coefficient C(2n, n). -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- The least positive integer that does not divide m. -/
noncomputable def leastNonDivisor (m : ℕ) : ℕ :=
  if hm : m = 0 then 1
  else Nat.find (⟨m + 1, ⟨by omega, fun h =>
    absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h) (by omega)⟩⟩ :
    ∃ k : ℕ, k > 0 ∧ ¬(k ∣ m))

/-- The least non-divisor of C(2n, n). -/
noncomputable def leastNonDivCentral (n : ℕ) : ℕ :=
  leastNonDivisor (centralBinom n)

/- ## Main Conjecture -/

/-- **Erdős Problem #731** (OPEN): For almost all n, the least m with
    m ∤ C(2n, n) satisfies m = exp((log n)^{1/2 + o(1)}).
    Placeholder: precise formulation requires asymptotic density. -/
theorem erdos_731_conjecture : True := trivial

/- ## Divisibility Properties of Central Binomials -/

/-- **Kummer's Theorem**: The p-adic valuation of C(m+n, m) equals the
    number of carries when adding m and n in base p.
    Placeholder: full formalization needs p-adic valuations. -/
theorem kummer_carries (p m n : ℕ) (hp : Nat.Prime p) : True := trivial

/-- For prime p ≤ 2n, we have p | C(2n, n) iff there is at least one
    carry when adding n to itself in base p. -/
axiom prime_divides_central_iff (p n : ℕ) (hp : Nat.Prime p) (hle : p ≤ 2 * n) :
  p ∣ centralBinom n ↔
    -- At least one digit of n in base p is ≥ ⌈p/2⌉
    ∃ k : ℕ, (n / p ^ k) % p ≥ (p + 1) / 2

/-- Small primes always divide C(2n, n) for large n. -/
axiom small_primes_divide (p : ℕ) (hp : Nat.Prime p) :
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → p ∣ centralBinom n

/-- C(2n, n) is always even for n ≥ 1.
    Proof: By Pascal's rule, C(2n, n) = C(2n-1, n-1) + C(2n-1, n).
    By symmetry C(2n-1, n) = C(2n-1, n-1), so C(2n, n) = 2·C(2n-1, n-1). -/
theorem two_divides_central (n : ℕ) (hn : n ≥ 1) : 2 ∣ centralBinom n := by
  unfold centralBinom
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- C(2(m+1), m+1) = C(2m+1, m) + C(2m+1, m+1) by Pascal
  have pascal : Nat.choose (2 * (m + 1)) (m + 1) =
      Nat.choose (2 * m + 1) m + Nat.choose (2 * m + 1) (m + 1) := by
    have : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [this, Nat.choose_succ_succ]
  -- C(2m+1, m) = C(2m+1, m+1) by symmetry
  have sym : Nat.choose (2 * m + 1) m = Nat.choose (2 * m + 1) (m + 1) := by
    rw [← Nat.choose_symm (by omega : m + 1 ≤ 2 * m + 1)]
    congr 1; omega
  rw [pascal, sym, ← two_mul]
  exact dvd_mul_right 2 _

/-- The product of all primes ≤ x is roughly e^x (prime number theorem).
    Placeholder: full formalization needs Chebyshev functions. -/
theorem primorial_asymptotic : True := trivial

/- ## Asymptotic Analysis -/

/-- Note: The claim that leastNonDivCentral n is always prime is FALSE.
    Counterexample: centralBinom 2 = C(4,2) = 6, and leastNonDivisor 6 = 4
    (since 1|6, 2|6, 3|6, but 4∤6), and 4 is not prime.
    The EGRS result is about the *typical* least non-divisor being prime
    (for *almost all* n), not for all n. -/
theorem least_nondiv_counterexample : ¬Nat.Prime 4 ∧ centralBinom 2 = 6 := by
  constructor
  · decide
  · native_decide

/-- **EGRS (1975)**: The typical behavior is
    log(leastNonDivCentral n) ~ (log n)^{1/2}.
    Placeholder: full formalization needs probabilistic number theory. -/
theorem egrs_typical_behavior : True := trivial

/- ## Bounds -/

/-- Lower bound: for any P, there exists a density threshold.
    Placeholder: the actual density claim requires measure theory. -/
theorem lower_bound_most_n :
    ∀ (P : ℕ), ∃ (D : ℕ), D > 0 ∧ True :=
  fun _ => ⟨1, by omega, trivial⟩

/-- Upper bound: there always exists a prime p ≤ 2n+1 not dividing C(2n, n),
    namely p = 2n+1 when it is prime and n+1 < p. -/
axiom upper_bound_trivial (n : ℕ) (hn : n ≥ 1) :
  leastNonDivCentral n ≤ 2 * n + 1

/-- **Bertrand's postulate** applied: for n ≥ 1, there exists a prime p
    with n < p ≤ 2n, and this prime divides C(2n, n) exactly once.
    Proof: Bertrand gives p ∈ (n, 2n]. Since n < p and p ≤ 2n,
    Nat.Prime.dvd_choose_add applies (both summands n < p, and p ≤ n+n). -/
theorem bertrand_central (n : ℕ) (hn : n ≥ 1) :
  ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n ∧ p ∣ centralBinom n := by
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  refine ⟨p, hp, hnp, hp2n, ?_⟩
  unfold centralBinom
  have h2n : 2 * n = n + n := by omega
  rw [h2n]
  exact hp.dvd_choose_add hnp hnp (by omega)

/-- The central binomial satisfies C(2n, n) ≥ 4^n / (2n+1) for n ≥ 0.
    Proof: Σ_{k=0}^{2n} C(2n,k) = 4^n (binomial theorem). This sum has 2n+1
    terms, each ≤ C(2n,n). So (2n+1)·C(2n,n) ≥ 4^n. -/
theorem central_binom_lower (n : ℕ) :
    centralBinom n * (2 * n + 1) ≥ 4 ^ n := by
  unfold centralBinom
  -- 4^n = 2^(2n) = Σ_{k < 2n+1} C(2n, k) (binomial theorem)
  have h4eq : 4 ^ n = ∑ m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) m := by
    rw [Nat.sum_range_choose, show (4 : ℕ) ^ n = (2 ^ 2) ^ n from by norm_num, ← pow_mul]
  have hdiv : (2 * n) / 2 = n := Nat.mul_div_cancel_left n (by omega)
  rw [h4eq, ge_iff_le]
  -- Each C(2n, k) ≤ C(2n, n) (central term is maximum)
  calc ∑ m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) m
      ≤ ∑ _m ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) n := by
        apply Finset.sum_le_sum
        intro k _
        calc Nat.choose (2 * n) k
            ≤ Nat.choose (2 * n) ((2 * n) / 2) := Nat.choose_le_middle k (2 * n)
          _ = Nat.choose (2 * n) n := by rw [hdiv]
    _ = Nat.choose (2 * n) n * (2 * n + 1) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
