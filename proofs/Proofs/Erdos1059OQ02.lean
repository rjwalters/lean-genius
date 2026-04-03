/-
Erdős Problem #1059, Open Question 02:
Selberg Sieve Approach to Factorial Subtraction Compositeness

## Problem

Can the Selberg sieve prove Erdős's alternative formulation?
Specifically: are there infinitely many n with l! < n ≤ (l+1)! such that
  (1) all prime factors of n exceed l, and
  (2) n - k! is composite for all 1 ≤ k ≤ l?

## Mathematical Context

Erdős's alternative approach (axiomatized in Problem.lean) claims such n exist
infinitely often. The Selberg sieve provides upper bounds on smooth integers
(those with all prime factors ≤ l) in [l!, (l+1)!], establishing condition (1).
Condition (2) is harder: large prime factors do NOT automatically imply n - k!
is composite.

The key obstruction: if we try to certify n - k! composite via a small prime
divisor q ≤ l, we need q | n. But the large-factor condition forbids this.
A more refined argument (e.g., CRT-based sieve choice of n) would be needed.

Axiom count: 1 (selberg_bound_large_factors — analytic number theory)
Sorry count: 2 (coprime lemmas, main implication)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Erdos1059OQ02

open Nat

/-!
## Definitions
-/

/-- Erdős's alternative formulation (same as in Problem.lean). -/
def ErdosAlternative : Prop :=
  Set.Infinite {n : ℕ | ∃ l : ℕ,
    Nat.factorial l < n ∧ n ≤ Nat.factorial (l + 1) ∧
    (∀ p : ℕ, p.Prime → p ∣ n → p > l) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ l → ¬(n - Nat.factorial k).Prime ∧ n - Nat.factorial k ≥ 2)}

/-!
## Elementary Structural Lemmas
-/

/-- The factorial interval (l!, (l+1)!] has size l * l! (since (l+1)! = (l+1) * l!). -/
theorem factorial_interval_size (l : ℕ) :
    Nat.factorial (l + 1) - Nat.factorial l = l * Nat.factorial l := by
  rw [Nat.factorial_succ, Nat.succ_mul]
  exact Nat.add_sub_cancel_right _ _

/-- A prime p > k cannot divide k!.
    Proof: induction on k; if p | (k+1) * k!, then either p | k+1 (giving p ≤ k+1,
    contradicting p > k+1) or p | k! (inductive case). -/
theorem prime_gt_not_dvd_factorial {p k : ℕ} (hp : p.Prime) (hpk : p > k) :
    ¬ p ∣ Nat.factorial k := by
  induction k with
  | zero =>
    simp [Nat.factorial]
    exact hp.one_lt.ne'
  | succ k ih =>
    rw [Nat.factorial_succ]
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · have : p ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) h
      omega
    · exact ih (by omega) h

/-- If all prime factors of n exceed l, then n is coprime to k! for any k ≤ l.
    Proof sketch: any common prime factor of n and k! divides k!, so is ≤ k ≤ l,
    contradicting the large-factor hypothesis. -/
theorem coprime_of_large_factors_lt {n l k : ℕ} (hkl : k ≤ l)
    (hn : ∀ p : ℕ, p.Prime → p ∣ n → p > l) :
    Nat.Coprime n (Nat.factorial k) := by
  -- Proof sketch: any common prime factor of n and k! divides k!, so is ≤ k ≤ l,
  -- contradicting the large-factor hypothesis on n.
  sorry

/-!
## The Selberg Sieve Bound

The Selberg sieve [Selberg 1947] upper bounds integers in (l!, (l+1)!] with a
prime factor ≤ l. The count of l-smooth integers in this interval is O(l! * π(l))
where π(l) = #{primes ≤ l} ≈ l/log l. Since the interval has size l * l!, the
fraction of smooth integers is O(1/log l) → 0. So infinitely many n satisfy (1).

This is analytic number theory not in Mathlib; stated as an axiom.
-/

/-- Selberg sieve: for each l ≥ 2, there exists n ∈ (l!, (l+1)!] with all prime factors > l. -/
axiom selberg_bound_large_factors (l : ℕ) (hl : l ≥ 2) :
    ∃ n : ℕ, Nat.factorial l < n ∧ n ≤ Nat.factorial (l + 1) ∧
    ∀ p : ℕ, p.Prime → p ∣ n → p > l

/-!
## The Key Obstruction to Condition (2)

**Claim**: The "small prime divisor" approach to proving n - k! composite fails
when n has all large prime factors.

If we want q | n - k! for some prime q ≤ k, we would need q | n (since q | k!
means q | n ↔ q | n - k!). But q ≤ k ≤ l contradicts the large-factor condition.
-/

/-- The direct small-factor certification approach fails: no prime q ≤ l divides n. -/
theorem large_factor_no_small_prime {n l : ℕ}
    (hn : ∀ p : ℕ, p.Prime → p ∣ n → p > l)
    {q : ℕ} (hq : q.Prime) (hql : q ≤ l) : ¬ q ∣ n := by
  intro h_dvd
  have := hn q hq h_dvd
  omega

/-- Consequence: if n has all prime factors > l, then for any k ≤ l,
    no prime q ≤ k can simultaneously divide n and certify n - k! composite
    via the small-prime route. -/
theorem small_prime_cert_impossible {n l k : ℕ} (hkl : k ≤ l)
    (hn : ∀ p : ℕ, p.Prime → p ∣ n → p > l)
    {q : ℕ} (hq : q.Prime) (hqk : q ≤ k) : ¬ q ∣ n :=
  large_factor_no_small_prime hn hq (hqk.trans hkl)

/-!
## Summary

1. Condition (1) — large prime factors — is achievable via the Selberg sieve
   (`selberg_bound_large_factors` axiom shows ∃ n in range with large factors for each l).

2. Condition (2) — composite subtractions — requires a different mechanism:
   - Small-prime certification fails for large-factor n (`small_prime_cert_impossible`)
   - A refined approach (e.g., choosing n via CRT to be divisible by specific large primes
     that happen to divide n - k!) is needed

3. Gap: The missing piece is a proof that n can be chosen satisfying BOTH (1) and (2)
   simultaneously. This likely requires a version of the Selberg sieve with
   congruence conditions — more powerful than the existence statement above.

This explains why `erdos_alternative_approach` in Problem.lean is still an axiom.
-/

/-- Main theorem: ErdosAlternative holds (requires full sieve + compositeness argument). -/
theorem erdos_alternative_holds : ErdosAlternative := by
  sorry

end Erdos1059OQ02
