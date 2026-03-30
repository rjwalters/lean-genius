/-
# Erdős Problem 685: Prime Divisors of Binomial Coefficients

For `ε > 0` and large `n`, if `n^ε < k ≤ n^{1-ε}`, is the number of
distinct prime divisors of `C(n,k)` equal to `(1 + o(1)) · k · ∑_{k<p<n} 1/p`?

A trivial lower bound is `ω(C(n,k)) > log C(n,k) / log n`, which is
asymptotically tight when `k > n^{1-o(1)}`.

*Reference:* [erdosproblems.com/685](https://www.erdosproblems.com/685)
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset Nat

/- ## Prime divisor count -/

/-- `omega n` is the number of distinct prime divisors of `n`. -/
noncomputable def omega (n : ℕ) : ℕ :=
    n.primeFactors.card

/-- The sum `∑_{k < p < n, p prime} 1/p`. -/
noncomputable def primeSumInRange (k n : ℕ) : ℝ :=
    ((Finset.Ioo k n).filter Nat.Prime).sum (fun p => (1 : ℝ) / p)

/- ## Main conjecture -/

/-- Erdős Problem 685: For `n^ε < k ≤ n^{1-ε}`, the number of distinct prime
divisors of `C(n,k)` is asymptotically `k · ∑_{k<p<n} 1/p`. -/
def ErdosProblem685 : Prop :=
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ δ : ℝ, 0 < δ →
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
          ∀ k : ℕ, (n : ℝ) ^ ε < k ∧ (k : ℝ) ≤ (n : ℝ) ^ (1 - ε) →
            (1 - δ) * k * primeSumInRange k n ≤ (omega (n.choose k) : ℝ) ∧
            (omega (n.choose k) : ℝ) ≤ (1 + δ) * k * primeSumInRange k n

/- ## Trivial lower bound -/

/-- Trivial lower bound: `ω(C(n,k)) > log C(n,k) / log n`. -/
/-- The lower bound is asymptotically tight for `k > n^{1-o(1)}`. -/
/- ## Basic properties -/

/-- `ω(1) = 0`: 1 has no prime divisors. -/
theorem omega_one : omega 1 = 0 := by
  simp [omega, Nat.primeFactors]

/-- `C(n,0) = 1`, so `ω(C(n,0)) = 0`. -/
theorem omega_choose_zero (n : ℕ) : omega (n.choose 0) = 0 := by
  rw [Nat.choose_zero_right]; exact omega_one

/-- `C(n,1) = n`, so `ω(C(n,1)) = ω(n)`. -/
theorem omega_choose_one (n : ℕ) : omega (n.choose 1) = omega n := by
  rw [Nat.choose_one_right]

/-- `ω(n) = 0` iff `n ≤ 1`. -/
theorem omega_eq_zero_iff (n : ℕ) : omega n = 0 ↔ n ≤ 1 := by
  simp only [omega, Finset.card_eq_zero]
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    -- n ≥ 2, so n has at least one prime factor
    have hn2 : 2 ≤ n := hn
    have := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    obtain ⟨p, hp, hpn⟩ := this
    have : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
    rw [h] at this
    exact Finset.notMem_empty p this
  · intro h
    interval_cases n <;> simp [Nat.primeFactors]

/-- `ω(n) > 0` for `n ≥ 2`. -/
theorem omega_pos_of_one_lt (n : ℕ) (hn : 1 < n) : 0 < omega n := by
  by_contra h
  push_neg at h
  have := (omega_eq_zero_iff n).mp (Nat.le_zero.mp h)
  omega

/-- `ω(p) = 1` for a prime `p`. -/
theorem omega_prime (p : ℕ) (hp : p.Prime) : omega p = 1 := by
  unfold omega
  have : p.primeFactors = {p} := by
    ext q
    simp only [Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · intro ⟨hq, hqp, _⟩
      exact (hp.eq_one_or_self_of_dvd q hqp).resolve_left (Nat.Prime.one_lt hq).ne'
    · intro heq; rw [heq]
      exact ⟨hp, dvd_refl p, hp.pos.ne'⟩
  rw [this, Finset.card_singleton]
