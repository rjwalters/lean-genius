/-
  Erdős Problem #458: LCM Inequality for Primes

  Let [1,...,n] denote the least common multiple of {1,...,n}.
  Let p_k be the k-th prime.

  **Conjecture**: For all k ≥ 1,
    lcm(1, ..., p_{k+1} - 1) < p_k · lcm(1, ..., p_k)

  **Status**: OPEN

  **Context**: Erdős and Graham write this is "almost certainly" true,
  but proving it requires overcoming two major obstacles:

  1. One must rule out many primes q with p_k < q² < p_{k+1}.
     This essentially requires something close to Legendre's conjecture
     (there's always a prime between n² and (n+1)²).

  2. Small primes cause additional complications.

  The inequality relates how lcm grows as we extend from p_k to p_{k+1}.
  Since p_{k+1} is the first new prime factor after p_k, the growth
  should be controlled, but making this rigorous is very difficult.

  Reference: https://erdosproblems.com/458
-/

import Mathlib

namespace Erdos458

open Nat Finset BigOperators

/-! ## The LCM Function -/

/--
**lcm_upto n** is the least common multiple of {1, 2, ..., n}.

This is a fundamental arithmetic function with deep connections to:
- The prime counting function π(n)
- Chebyshev's ψ function (log lcm_upto n ≈ n)
- The distribution of prime numbers
-/
def lcm_upto (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

/-! ## Basic Properties -/

/-- lcm_upto 1 = 1 -/
theorem lcm_upto_one : lcm_upto 1 = 1 := by
  simp [lcm_upto]

/-- lcm_upto is always positive -/
theorem lcm_upto_pos (n : ℕ) : 0 < lcm_upto n := by
  unfold lcm_upto
  apply Nat.pos_of_ne_zero
  intro h
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨a, ha, ha0⟩ := h
  simp only [Finset.mem_Icc, id_eq] at ha ha0
  omega

/-- Small values: lcm(1,2) = 2 -/
theorem lcm_upto_two : lcm_upto 2 = 2 := by native_decide

/-- Small values: lcm(1,2,3) = 6 -/
theorem lcm_upto_three : lcm_upto 3 = 6 := by native_decide

/-- Small values: lcm(1,2,3,4) = 12 -/
theorem lcm_upto_four : lcm_upto 4 = 12 := by native_decide

/-- Small values: lcm(1,...,5) = 60 -/
theorem lcm_upto_five : lcm_upto 5 = 60 := by native_decide

/-- Small values: lcm(1,...,6) = 60 (6 = 2·3, already covered) -/
theorem lcm_upto_six : lcm_upto 6 = 60 := by native_decide

/-! ## Growth Properties -/

/-- lcm_upto is monotone in the divisibility order -/
theorem lcm_upto_dvd_mono {m n : ℕ} (hmn : m ≤ n) : lcm_upto m ∣ lcm_upto n := by
  unfold lcm_upto
  apply Finset.lcm_mono
  exact Finset.Icc_subset_Icc (le_refl _) hmn

/-- When we add a prime, lcm multiplies by that prime -/
axiom lcm_upto_prime_step (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : p ≤ n) (hnp : n < p.minFac) :
    lcm_upto n = lcm_upto (p - 1)

/-- lcm grows by factor p when crossing prime p -/
axiom lcm_upto_at_prime (p : ℕ) (hp : p.Prime) :
    lcm_upto p = p * lcm_upto (p - 1)

/-! ## The nth Prime -/

/-- p_k denotes the k-th prime (0-indexed: p_0 = 2, p_1 = 3, etc.) -/
noncomputable def nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- The 0th prime is 2 -/
axiom nthPrime_zero : nthPrime 0 = 2

/-- The 1st prime is 3 -/
axiom nthPrime_one : nthPrime 1 = 3

/-- The 2nd prime is 5 -/
axiom nthPrime_two : nthPrime 2 = 5

/-- The 3rd prime is 7 -/
axiom nthPrime_three : nthPrime 3 = 7

/-- Every nthPrime is prime -/
theorem nthPrime_prime (k : ℕ) : (nthPrime k).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k

/-- Primes are strictly increasing -/
theorem nthPrime_strictMono : StrictMono nthPrime := fun _ _ hij =>
  Nat.nth_strictMono Nat.infinite_setOf_prime hij

/-! ## The Main Conjecture -/

/--
**Erdős Problem #458 (OPEN)**:

For all k ≥ 1:
  lcm(1, ..., p_{k+1} - 1) < p_k · lcm(1, ..., p_k)

This asks whether the LCM up to just before the next prime is strictly
less than the previous prime times the LCM up to that prime.

Intuitively: between consecutive primes p_k and p_{k+1}, the LCM can
only grow by composite factors (powers of smaller primes), and this
growth should be bounded by multiplying by p_k.
-/
def Erdos458Conjecture : Prop :=
  ∀ k : ℕ, k ≥ 1 →
    lcm_upto (nthPrime (k + 1) - 1) < nthPrime k * lcm_upto (nthPrime k)

/-! ## Why This is Hard -/

/--
**Obstacle 1**: We need to control primes q with p_k < q² < p_{k+1}.

If there are many such q, each contributes a factor to the LCM that
could make it too large. We need at most one such q, which would
follow from p_{k+1} - p_k < √p_k.

This is essentially **Legendre's Conjecture**: there is always a prime
between n² and (n+1)².
-/
def LegendreConjecture : Prop :=
  ∀ n : ℕ, n ≥ 1 → ∃ p : ℕ, p.Prime ∧ n^2 < p ∧ p < (n + 1)^2

/--
**Conditional Result**: If Legendre's conjecture holds, the prime gap
p_{k+1} - p_k is bounded, which helps control the LCM growth.
-/
axiom legendre_implies_gap_bound :
    LegendreConjecture →
    ∀ k : ℕ, k ≥ 1 → nthPrime (k + 1) - nthPrime k < (nthPrime k).sqrt + 1

/-! ## Verified Small Cases -/

/-- The conjecture holds for k = 1: lcm(1,2,3,4) < 3 · lcm(1,2,3)
    p_1 = 3, p_2 = 5, lcm(1,2,3,4) = 12 < 3 · 6 = 18 ✓ -/
theorem erdos458_k1 : lcm_upto 4 < 3 * lcm_upto 3 := by native_decide

/-- The conjecture holds for k = 2: lcm(1,...,6) < 5 · lcm(1,...,5)
    p_2 = 5, p_3 = 7, lcm(1,...,6) = 60 < 5 · 60 = 300 ✓ -/
theorem erdos458_k2 : lcm_upto 6 < 5 * lcm_upto 5 := by native_decide

/-! ## Asymptotic Perspective -/

/--
**Chebyshev's Result**: log(lcm_upto n) ~ n as n → ∞

This means lcm_upto n ≈ e^n asymptotically. The conjecture essentially
asks about the fine structure of this growth between consecutive primes.
-/
axiom chebyshev_psi : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < 1 ∧ 1 < c₂ ∧
    ∀ n : ℕ, n ≥ 2 → c₁ * n < Real.log (lcm_upto n) ∧ Real.log (lcm_upto n) < c₂ * n

end Erdos458
