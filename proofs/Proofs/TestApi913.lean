import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

open Nat Finset

-- Original definition
def HasDistinctExponents913 (n : ℕ) : Prop :=
  Set.InjOn (n * (n + 1)).factorization (n * (n + 1)).primeFactors

-- Proof for n = 3: 3*4 = 12 = 2^2 * 3, exponents {2,1} distinct
theorem example_n3_913 : HasDistinctExponents913 3 := by
  unfold HasDistinctExponents913
  intro a ha b hb hab
  simp only [show 3 * (3 + 1) = 12 from by norm_num] at *
  have h12pf : (12 : ℕ).primeFactors = {2, 3} := by native_decide
  rw [h12pf] at ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  have hf2 : (12 : ℕ).factorization 2 = 2 := by native_decide
  have hf3 : (12 : ℕ).factorization 3 = 1 := by native_decide
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
