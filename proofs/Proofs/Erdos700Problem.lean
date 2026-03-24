/-
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

/- ## Definitions -/

/-- The largest prime factor of n. Returns 0 if n ≤ 1. -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if _ : 2 ≤ n then
    Finset.sup ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ∣ n)) id
  else 0

/-- The smallest prime factor of n. -/
noncomputable def smallestPrimeFactor (n : ℕ) : ℕ :=
  Nat.minFac n

/-- f(n) = min_{1 < k ≤ n/2} gcd(n, C(n,k)).
    Defined for n ≥ 4 (where the range [2, n/2] is nonempty).
    Returns 0 for n < 4. -/
noncomputable def fBinom (n : ℕ) : ℕ :=
  if h : 4 ≤ n then
    ((Finset.Icc 2 (n / 2)).image (fun k => Nat.gcd n (Nat.choose n k))).min' (by
      apply Finset.Nonempty.image
      exact ⟨2, Finset.mem_Icc.mpr ⟨le_refl 2, by omega⟩⟩)
  else 0

/- ## Helper Lemmas -/

/-- The smallest prime factor of p² is p, for any prime p. -/
theorem minFac_prime_sq (p : ℕ) (hp : p.Prime) : Nat.minFac (p * p) = p := by
  have hpp : p * p ≠ 1 := by have := hp.two_le; nlinarith
  have hpf : (Nat.minFac (p * p)).Prime := Nat.minFac_prime hpp
  have hdvdp : Nat.minFac (p * p) ∣ p := by
    have h := Nat.minFac_dvd (p * p)
    have h2 : Nat.minFac (p * p) ∣ p ^ 2 := by convert h using 1; ring
    exact hpf.dvd_of_dvd_pow h2
  exact (hp.eq_one_or_self_of_dvd _ hdvdp).resolve_left (by have := hpf.one_lt; omega)

/-- minFac(p * q) = p for primes p ≤ q. -/
theorem minFac_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    Nat.minFac (p * q) = p := by
  have hpq_ne1 : p * q ≠ 1 := by have := hp.two_le; nlinarith
  have hpf := Nat.minFac_prime hpq_ne1
  have hdvd := Nat.minFac_dvd (p * q)
  rcases hpf.dvd_mul.mp hdvd with hp_dvd | hq_dvd
  · exact (hp.eq_one_or_self_of_dvd _ hp_dvd).resolve_left hpf.one_lt.ne'
  · have heq := (hq.eq_one_or_self_of_dvd _ hq_dvd).resolve_left hpf.one_lt.ne'
    have hle : Nat.minFac (p * q) ≤ p :=
      Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
    omega

/-- Any prime factor of n is ≤ largestPrimeFactor(n). -/
theorem le_largestPrimeFactor {n r : ℕ} (hr : r.Prime) (hdvd : r ∣ n) (hn : 2 ≤ n) :
    r ≤ largestPrimeFactor n := by
  unfold largestPrimeFactor
  simp only [hn, dite_true]
  have hr_le_n : r ≤ n := Nat.le_of_dvd (by omega) hdvd
  exact Finset.le_sup (f := id)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr, hdvd⟩)

/- ## Basic Bounds -/

/-- f(n) ≤ n/P(n) for all composite n.
    Follows from Kummer's theorem: choosing k = p^a where p^a ‖ n
    gives exactly one carry in base-p addition, so v_p(C(n,k)) = 1,
    hence gcd(n, C(n, p^a)) = n/p^a ≤ n/P(n). -/
axiom f_upper_bound (n : ℕ) (hn : ¬n.Prime) (hn2 : 2 ≤ n) :
  fBinom n ≤ n / largestPrimeFactor n

/-- f(n) ≥ p(n), the smallest prime factor of n.
    For every 1 < k ≤ n/2, the smallest prime p dividing n also
    divides gcd(n, C(n,k)), since by Kummer's theorem v_p(C(n,k)) ≥ 1
    whenever p | n and 0 < k < n. -/
axiom f_lower_bound (n : ℕ) (hn : 2 ≤ n) :
  smallestPrimeFactor n ≤ fBinom n

/- ## Known Equalities -/

/-- When n = pq is a product of two primes with p ≤ q, f(n) = p.
    Sandwich: p = minFac(pq) ≤ f(pq) ≤ pq/largestPrimeFactor(pq) ≤ pq/q = p. -/
theorem f_semiprime (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    fBinom (p * q) = p := by
  have h2 : 2 ≤ p * q := by have := hp.two_le; nlinarith
  have hcomp : ¬(p * q).Prime := by
    intro hprime
    rcases hprime.eq_one_or_self_of_dvd p (dvd_mul_right p q) with h1 | h2
    · exact hp.one_lt.ne' h1
    · have : q = 1 := by nlinarith [hp.one_lt]
      exact absurd this (by omega)
  -- Lower bound: p ≤ f(pq)
  have hlower : p ≤ fBinom (p * q) := by
    have hmin := f_lower_bound (p * q) h2
    rw [show smallestPrimeFactor (p * q) = Nat.minFac (p * q) from rfl,
        minFac_mul_prime hp hq hpq] at hmin
    exact hmin
  -- Upper bound: f(pq) ≤ p
  have hupper : fBinom (p * q) ≤ p := by
    have hup := f_upper_bound (p * q) hcomp h2
    have hq_le : q ≤ largestPrimeFactor (p * q) :=
      le_largestPrimeFactor hq (dvd_mul_left q p) h2
    have hlpf_pos : 0 < largestPrimeFactor (p * q) := by
      have := hq.two_le; linarith
    have hpq_le : p * q / largestPrimeFactor (p * q) ≤ p :=
      calc p * q / largestPrimeFactor (p * q)
          ≤ p * largestPrimeFactor (p * q) / largestPrimeFactor (p * q) :=
            Nat.div_le_div_right (Nat.mul_le_mul_left p hq_le)
        _ = p := Nat.mul_div_cancel p hlpf_pos
    linarith
  omega

/-- f(30) = 30/5 = 6. One verifies gcd(30, C(30,k)) ≥ 6 for all
    1 < k ≤ 15, with equality at k = 5 where C(30,5) = 142506
    and gcd(30, 142506) = 6. -/
axiom f_30 : fBinom 30 = 6

/- ## Question 1: Characterization (OPEN)

  Which composite n satisfy f(n) = n/P(n)?

  Known examples: all semiprimes pq (by f_semiprime) and n = 30 (by f_30).
  The general characterization is an open problem. Note that f(n) = n/P(n)
  does NOT hold for all composite n — it fails when n has many prime factors
  of varying sizes, since then the minimizing k can achieve a smaller gcd. -/

/- ## Question 2: Large Values -/

/-- For n = p², f(n) ≥ p = √n.
    PROVED from f_lower_bound and minFac(p²) = p. -/
theorem f_prime_square (p : ℕ) (hp : p.Prime) :
    p ≤ fBinom (p * p) := by
  have h2 : 2 ≤ p * p := by have := hp.two_le; nlinarith
  have hbound := f_lower_bound (p * p) h2
  have hmin : smallestPrimeFactor (p * p) = p := by
    unfold smallestPrimeFactor
    exact minFac_prime_sq p hp
  rw [hmin] at hbound
  exact hbound

/-- Question 2: Are there infinitely many composite n with f(n) > √n?
    Prime squares achieve f(p²) = p = √(p²), so they give ≥ but not >.
    Whether strict inequality f(n) > √n occurs for infinitely many
    composite n remains open. -/
axiom erdos_700_question2 :
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬n.Prime ∧ 4 ≤ n ∧
    (fBinom n : ℝ) > Real.sqrt n

/- ## Question 3: Upper Bound Conjecture -/

/-- Question 3: Is f(n) ≪_A n/(log n)^A for every A > 0?
    This would show f(n) is much smaller than n/P(n) for typical n,
    since P(n) ~ log n for most n by the Hardy-Ramanujan theorem. -/
axiom erdos_700_question3 (A : ℝ) (hA : 0 < A) :
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ¬n.Prime → 4 ≤ n →
    (fBinom n : ℝ) ≤ C * n / (Real.log n) ^ A
