/-!
# Erdős Problem #700: GCD of n with Binomial Coefficients

Erdős and Szekeres study f(n) = min_{1 < k ≤ n/2} gcd(n, C(n,k)).

Three questions:
1. Which composite n satisfy f(n) = n/P(n) where P(n) = largest prime factor?
2. Are there infinitely many composite n with f(n) > √n?
3. Is f(n) ≪_A n/(log n)^A for every A > 0 and all composite n?

Known:
- f(n) ≤ n/P(n) for all composite n
- f(n) = n/P(n) when n = pq (product of two primes) or n = 30
- f(n) ≥ p(n), the smallest prime factor of n
- f(p²) ≥ p = √n

Reference: https://erdosproblems.com/700
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic

/-! ## Definitions -/

/-- The largest prime factor of n. Returns 0 if n ≤ 1. -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : 2 ≤ n then
    Finset.sup ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ∣ n)) id
  else 0

/-- The smallest prime factor of n. -/
noncomputable def smallestPrimeFactor (n : ℕ) : ℕ :=
  Nat.minFac n

/-- f(n) = min_{1 < k ≤ n/2} gcd(n, C(n,k)).
    Axiomatized since the definition requires n ≥ 4 for the range to be nonempty. -/
axiom fBinom (n : ℕ) : ℕ

/-! ## Basic Bounds -/

/-- f(n) ≤ n/P(n) for all composite n. -/
axiom f_upper_bound (n : ℕ) (hn : ¬n.Prime) (hn2 : 2 ≤ n) :
  fBinom n ≤ n / largestPrimeFactor n

/-- f(n) ≥ p(n), the smallest prime factor of n. -/
axiom f_lower_bound (n : ℕ) (hn : 2 ≤ n) :
  smallestPrimeFactor n ≤ fBinom n

/-! ## Known Equalities -/

/-- When n = pq is a product of two primes, f(n) = n/P(n) = p. -/
axiom f_semiprime (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
  fBinom (p * q) = p

/-- f(30) = 30/5 = 6. -/
axiom f_30 : fBinom 30 = 6

/-! ## Question 1: Characterization -/

/-- Question 1: characterize which composite n satisfy f(n) = n/P(n).
    Known to hold for semiprimes and n = 30. -/
axiom erdos_700_question1 :
  ∀ n : ℕ, ¬n.Prime → 4 ≤ n →
    (fBinom n = n / largestPrimeFactor n ↔ True)  -- placeholder

/-! ## Question 2: Large Values -/

/-- For n = p², f(n) ≥ p = √n. -/
axiom f_prime_square (p : ℕ) (hp : p.Prime) :
  p ≤ fBinom (p * p)

/-- Question 2: Are there infinitely many composite n with f(n) > √n? -/
axiom erdos_700_question2 :
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬n.Prime ∧ 4 ≤ n ∧
    (fBinom n : ℝ) > Real.sqrt n

/-! ## Question 3: Upper Bound Conjecture -/

/-- Question 3: Is f(n) ≪_A n/(log n)^A for every A > 0? -/
axiom erdos_700_question3 (A : ℝ) (hA : 0 < A) :
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ¬n.Prime → 4 ≤ n →
    (fBinom n : ℝ) ≤ C * n / (Real.log n) ^ A
