-- Test API availability for Erdos889
import Mathlib

-- Check how to get factorization positivity from primeFactors membership
#check @Nat.mem_primeFactors
#check @Nat.Prime.factorization_pos_of_dvd

-- Test vShifted_zero proof approach
noncomputable def newPrimeFactorCount' (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter (fun p =>
    ∀ i ∈ Finset.range k, ¬ p ∣ n + i)).card

noncomputable def v₀' (n : ℕ) : ℕ :=
  ⨆ k ∈ Finset.range (n + 1), newPrimeFactorCount' n k

noncomputable def vShifted' (l n : ℕ) : ℕ :=
  ⨆ k ∈ Finset.range (n + 1 - l), newPrimeFactorCount' n (k + l)

theorem test_vShifted_zero (n : ℕ) : vShifted' 0 n = v₀' n := by
  simp [vShifted', v₀']

-- Test factorization pos
example (p m : ℕ) (h : p ∈ m.primeFactors) : 0 < m.factorization p := by
  obtain ⟨hp, hpm, hm⟩ := Nat.mem_primeFactors.mp h
  exact Nat.Prime.factorization_pos_of_dvd hp hm hpm

-- Test dvd_pow_self
example (p : ℕ) (n : ℕ) (hn : n ≠ 0) : p ∣ p ^ n := dvd_pow_self p hn
