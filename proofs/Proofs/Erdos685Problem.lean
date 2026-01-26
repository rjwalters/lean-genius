/-!
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

/-! ## Prime divisor count -/

/-- `omega n` is the number of distinct prime divisors of `n`. -/
noncomputable def omega (n : ℕ) : ℕ :=
    n.primeFactors.card

/-- The sum `∑_{k < p < n, p prime} 1/p`. -/
noncomputable def primeSumInRange (k n : ℕ) : ℝ :=
    ((Finset.Ioo k n).filter Nat.Prime).sum (fun p => (1 : ℝ) / p)

/-! ## Main conjecture -/

/-- Erdős Problem 685: For `n^ε < k ≤ n^{1-ε}`, the number of distinct prime
divisors of `C(n,k)` is asymptotically `k · ∑_{k<p<n} 1/p`. -/
def ErdosProblem685 : Prop :=
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ δ : ℝ, 0 < δ →
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
          ∀ k : ℕ, (n : ℝ) ^ ε < k ∧ (k : ℝ) ≤ (n : ℝ) ^ (1 - ε) →
            (1 - δ) * k * primeSumInRange k n ≤ (omega (n.choose k) : ℝ) ∧
            (omega (n.choose k) : ℝ) ≤ (1 + δ) * k * primeSumInRange k n

/-! ## Trivial lower bound -/

/-- Trivial lower bound: `ω(C(n,k)) > log C(n,k) / log n`. -/
axiom omega_choose_lower (n k : ℕ) (hn : 2 ≤ n) (hk : 0 < k) (hkn : k ≤ n) :
    Real.log (n.choose k : ℝ) / Real.log n ≤ (omega (n.choose k) : ℝ)

/-- The lower bound is asymptotically tight for `k > n^{1-o(1)}`. -/
axiom omega_choose_tight_near_n :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∀ k : ℕ, (n : ℝ) ^ (1 - ε) < k → k ≤ n →
          (omega (n.choose k) : ℝ) ≤
            (1 + ε) * Real.log (n.choose k : ℝ) / Real.log n

/-! ## Basic properties -/

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
axiom omega_eq_zero_iff (n : ℕ) : omega n = 0 ↔ n ≤ 1
