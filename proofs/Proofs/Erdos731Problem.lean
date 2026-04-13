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

/-- C(2n, n) > 0 for all n. -/
theorem centralBinom_pos (n : ℕ) : 0 < centralBinom n := by
  unfold centralBinom; exact Nat.choose_pos (by omega)

/-- C(0, 0) = 1. -/
theorem centralBinom_zero : centralBinom 0 = 1 := by native_decide

/-- C(2, 1) = 2. -/
theorem centralBinom_one : centralBinom 1 = 2 := by native_decide

/-- C(4, 2) = 6. -/
theorem centralBinom_two : centralBinom 2 = 6 := by native_decide

/-- C(6, 3) = 20. -/
theorem centralBinom_three : centralBinom 3 = 20 := by native_decide

/-- C(8, 4) = 70. -/
theorem centralBinom_four : centralBinom 4 = 70 := by native_decide

/-- C(10, 5) = 252. -/
theorem centralBinom_five : centralBinom 5 = 252 := by native_decide

/- ## Main Conjecture -/

/- **Erdős Problem #731** (OPEN): For almost all n, the least m with
    m ∤ C(2n, n) satisfies m = exp((log n)^{1/2 + o(1)}).
    Placeholder: precise formulation requires asymptotic density. -/

/- ## Divisibility Properties of Central Binomials -/

/- **Kummer's Theorem**: The p-adic valuation of C(m+n, m) equals the
    number of carries when adding m and n in base p.
    Placeholder: full formalization needs p-adic valuations. -/

/-- For prime p ≤ 2n, we have p | C(2n, n) iff there is at least one
    carry when adding n to itself in base p. -/
axiom prime_divides_central_iff (p n : ℕ) (hp : Nat.Prime p) (hle : p ≤ 2 * n) :
  p ∣ centralBinom n ↔
    -- At least one digit of n in base p is ≥ ⌈p/2⌉
    ∃ k : ℕ, (n / p ^ k) % p ≥ (p + 1) / 2

/-- The claim "for each prime p, p | C(2n,n) for all sufficiently large n"
    is FALSE for p ≥ 3. Counterexample: n = p^k gives 0 carries in base-p
    addition (Kummer), so p ∤ C(2·p^k, p^k) for all k.
    Concrete: C(6,3) = 20 and 3 ∤ 20. The correct statement is that
    the set {n : p ∤ C(2n,n)} has density 0 (most n have a large digit). -/
theorem small_primes_divide_false :
    ¬(3 ∣ centralBinom 3) ∧ centralBinom 3 = 20 := by
  constructor
  · unfold centralBinom; native_decide
  · unfold centralBinom; native_decide

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

/- The product of all primes ≤ x is roughly e^x (prime number theorem).
    Placeholder: full formalization needs Chebyshev functions. -/

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

/- **EGRS (1975)**: The typical behavior is
    log(leastNonDivCentral n) ~ (log n)^{1/2}.
    Placeholder: full formalization needs probabilistic number theory. -/

/- ## Bounds -/

/-- Lower bound: for any P, there exists a density threshold.
    Placeholder: the actual density claim requires measure theory. -/
theorem lower_bound_most_n :
    ∀ (P : ℕ), ∃ (D : ℕ), D > 0 ∧ True :=
  fun _ => ⟨1, by omega, trivial⟩

/-- C(N, k) divides lcm(1, ..., N) for k ≤ N.
    Proof (not yet formalized): By Kummer's theorem, v_p(C(N,k)) = number of carries
    when adding k and N-k in base p. The number of carries ≤ floor(log_p N),
    which equals v_p(lcm(1,...,N)). So v_p(C(N,k)) ≤ v_p(lcm(1,...,N)) for all primes p,
    hence C(N,k) | lcm(1,...,N).
    See also: Nair (1982), integral proof via Beta function identity. -/
axiom choose_dvd_lcm (N k : ℕ) (hk : k ≤ N) :
  Nat.choose N k ∣ (Finset.range (N + 1)).lcm id

/-- Upper bound: leastNonDivCentral n ≤ 2n+1 for all n ≥ 1.
    Proof: If all m ∈ {1,...,2n+1} divide C(2n,n), then lcm(1,...,2n+1) ≤ C(2n,n).
    But C(2n+1,n) | lcm(1,...,2n+1) [choose_dvd_lcm] and
    C(2n+1,n) > C(2n,n) [choose_succ_gt_central], contradiction.
    Note: (2n+1) itself CAN divide C(2n,n) when composite (e.g. n=577). -/
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

/-- A prime larger than 2n does not divide C(2n, n).
    Proof: C(2n,n) · n! · n! = (2n)!, so C(2n,n) | (2n)!.
    But primes > 2n do not divide (2n)! (Legendre). -/
theorem prime_gt_not_dvd_central {p n : ℕ} (hp : Nat.Prime p) (hpn : 2 * n < p) :
    ¬(p ∣ centralBinom n) := by
  unfold centralBinom
  intro hd
  have hfact := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n from by omega] at hfact
  have hdvd_fact : p ∣ (2 * n).factorial := by
    have h1 : p ∣ Nat.choose (2 * n) n * n.factorial * n.factorial :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
    rwa [hfact] at h1
  exact absurd (hp.dvd_factorial.mp hdvd_fact) (by omega)

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

/- ## Key Structural Results -/

/-- The absorption identity for central binomials:
    (n+1) · C(2n+1, n) = (2n+1) · C(2n, n). -/
theorem central_binom_succ_identity (n : ℕ) :
    (n + 1) * Nat.choose (2 * n + 1) n = (2 * n + 1) * centralBinom n := by
  unfold centralBinom
  have hab := Nat.add_one_mul_choose_eq (2 * n) n
  -- hab : (2n+1) * C(2n, n) = C(2n+1, n+1) * (n+1)
  have hsym : Nat.choose (2 * n + 1) (n + 1) = Nat.choose (2 * n + 1) n := by
    rw [← Nat.choose_symm (by omega : n ≤ 2 * n + 1)]
    congr 1; omega
  rw [hsym] at hab
  -- hab : (2n+1) * C(2n, n) = C(2n+1, n) * (n+1)
  linarith [mul_comm (Nat.choose (2 * n + 1) n) (n + 1)]

/-- 2n+1 and n+1 are coprime: gcd(2n+1, n+1) = 1.
    Proof: any d dividing both must divide 2(n+1) - (2n+1) = 1. -/
theorem coprime_two_n_succ_n_succ (n : ℕ) : Nat.Coprime (2 * n + 1) (n + 1) := by
  suffices h : Nat.gcd (n + 1) (2 * n + 1) = 1 by rwa [Nat.coprime_comm]
  apply Nat.dvd_one.mp
  have h1 : Nat.gcd (n + 1) (2 * n + 1) ∣ n + 1 := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (n + 1) (2 * n + 1) ∣ 2 * n + 1 := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd (n + 1) (2 * n + 1) ∣ 2 * (n + 1) := dvd_mul_of_dvd_right h1 2
  have h4 : Nat.gcd (n + 1) (2 * n + 1) ∣ 2 * (n + 1) - (2 * n + 1) :=
    Nat.dvd_sub h3 h2
  rwa [show 2 * (n + 1) - (2 * n + 1) = 1 from by omega] at h4

/-- If (2n+1) | C(2n,n), then (2n+1)² | C(2n+1,n).
    Key reduction for the upper bound problem. -/
theorem dvd_central_implies_sq_dvd (n : ℕ) (hdvd : (2 * n + 1) ∣ centralBinom n) :
    (2 * n + 1) ^ 2 ∣ Nat.choose (2 * n + 1) n := by
  have hid := central_binom_succ_identity n
  obtain ⟨q, hq⟩ := hdvd
  unfold centralBinom at hq
  -- From identity and hq: (n+1) * C(2n+1,n) = (2n+1) * (2n+1) * q
  have hsq_dvd : (2 * n + 1) * (2 * n + 1) ∣ Nat.choose (2 * n + 1) n * (n + 1) := by
    refine ⟨q, ?_⟩
    -- Use a fresh copy of the identity with centralBinom expanded
    have h := central_binom_succ_identity n
    unfold centralBinom at h
    rw [hq] at h
    linarith
  rw [sq]
  exact (Nat.Coprime.mul_left (coprime_two_n_succ_n_succ n)
    (coprime_two_n_succ_n_succ n)).dvd_of_dvd_mul_right hsq_dvd

/-- For prime p and 0 < k < p, p² does not divide C(p, k).
    Since C(p,k)·k!·(p-k)! = p! and v_p(p!) = 1, p² cannot divide C(p,k). -/
theorem prime_sq_not_dvd_choose {p k : ℕ} (hp : Nat.Prime p) (hk0 : 0 < k) (hkp : k < p) :
    ¬(p ^ 2 ∣ Nat.choose p k) := by
  intro h
  have hfact := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt hkp)
  -- p^2 | C(p,k) * k! * (p-k)! = p!
  have hvp : p ^ 2 ∣ p.factorial := by
    calc p ^ 2 ∣ Nat.choose p k * k.factorial * (p - k).factorial :=
            dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
      _ = p.factorial := hfact
  -- p! = p * (p-1)!, so p^2 | p*(p-1)! means p | (p-1)!, contradicting p > p-1.
  have hpf : p.factorial = p * (p - 1).factorial := by
    cases p with
    | zero => exact absurd hp.pos (by omega)
    | succ n => simp [Nat.factorial_succ]
  rw [hpf, sq] at hvp
  have := (Nat.mul_dvd_mul_iff_left hp.pos).mp hvp
  exact absurd (hp.dvd_factorial.mp this) (by omega)

/-- When 2n+1 is prime, it does not divide C(2n, n).
    Direct proof: prime (2n+1) > 2n, so prime_gt_not_dvd_central applies. -/
theorem not_dvd_central_prime (n : ℕ) (hn : n ≥ 1) (hp : Nat.Prime (2 * n + 1)) :
    ¬((2 * n + 1) ∣ centralBinom n) :=
  prime_gt_not_dvd_central hp (by omega)

/-- Alternative proof via the identity: if (2n+1) | C(2n,n) then
    (2n+1)² | C(2n+1, n), contradicting v_p(C(p,k)) = 1 for prime p. -/
theorem not_dvd_central_prime_alt (n : ℕ) (hn : n ≥ 1) (hp : Nat.Prime (2 * n + 1)) :
    ¬((2 * n + 1) ∣ centralBinom n) := by
  intro hdvd
  exact absurd (dvd_central_implies_sq_dvd n hdvd)
    (prime_sq_not_dvd_choose hp (by omega) (by omega))

/-- C(2n+1, n) > C(2n, n) for n ≥ 1.
    By Pascal: C(2n+1, n) = C(2n, n-1) + C(2n, n), and C(2n, n-1) ≥ 1.
    This is step 2 of the lcm strategy for upper_bound_trivial. -/
theorem choose_succ_gt_central (n : ℕ) (hn : n ≥ 1) :
    Nat.choose (2 * n + 1) n > centralBinom n := by
  unfold centralBinom
  have hpascal : Nat.choose (2 * n + 1) n =
      Nat.choose (2 * n) (n - 1) + Nat.choose (2 * n) n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [show m + 1 - 1 = m from by omega]
    exact Nat.choose_succ_succ (2 * (m + 1)) m
  have hpos : Nat.choose (2 * n) (n - 1) ≥ 1 := Nat.choose_pos (by omega)
  omega
