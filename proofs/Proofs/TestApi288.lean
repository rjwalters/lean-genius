-- Test API availability for Erdős 288 proof
import Mathlib.Data.Rat.Defs
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open Finset BigOperators

-- Test 1: basic rational arithmetic
example : (3 : ℚ)⁻¹ + (4 : ℚ)⁻¹ + (5 : ℚ)⁻¹ + (6 : ℚ)⁻¹ + (20 : ℚ)⁻¹ = 1 := by
  norm_num

-- Test 2: Finset.Icc equality
example : Finset.Icc 3 6 = {3, 4, 5, 6} := by decide

-- Test 3: Prove the example by manually unfolding the sum
example :
    ∑ n ∈ (Finset.Icc 3 6 : Finset ℕ), (n : ℚ)⁻¹ +
    ∑ n ∈ (Finset.Icc 20 20 : Finset ℕ), (n : ℚ)⁻¹ = 1 := by
  have h1 : Finset.Icc 3 6 = {3, 4, 5, 6} := by decide
  have h2 : Finset.Icc 20 20 = {20} := by decide
  rw [h1, h2]
  simp only [Finset.sum_singleton]
  have hm1 : (3 : ℕ) ∉ ({4, 5, 6} : Finset ℕ) := by decide
  have hm2 : (4 : ℕ) ∉ ({5, 6} : Finset ℕ) := by decide
  have hm3 : (5 : ℕ) ∉ ({6} : Finset ℕ) := by decide
  simp only [Finset.sum_insert hm1, Finset.sum_insert hm2,
    Finset.sum_insert hm3, Finset.sum_singleton]
  norm_num
