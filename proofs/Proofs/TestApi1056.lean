/-
Test proof approach for Erdős 1056.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

def intervalProd' (a b : ℕ) : ℕ :=
  (Finset.Ico a b).prod id

def IsValidBoundary' (boundaries : List ℕ) (k : ℕ) : Prop :=
  boundaries.length = k + 1 ∧ boundaries.IsChain (· < ·)

/-- Uses `getD` (default `0` out of range) instead of `get` with an inline
`by omega` index proof: with only `i : Fin k` in scope there is no hypothesis
relating `k` to `boundaries.length`, so an index-bound proof is not derivable
in general at definition time (it only holds once `IsValidBoundary'` is also
known, which callers supply). `getD`/`get` agree on all in-range indices, so
this is definitionally faithful whenever `IsValidBoundary'` holds. -/
def AllProductsCongruentOne' (p : ℕ) (boundaries : List ℕ) (k : ℕ) : Prop :=
  IsValidBoundary' boundaries k ∧
  ∀ i : Fin k, intervalProd' (boundaries.getD i.val 0) (boundaries.getD (i.val + 1) 0) % p = 1

def HasSolution' (k : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ boundaries : List ℕ,
    AllProductsCongruentOne' p boundaries k

-- Test: Can we prove HasSolution' 2?
theorem test_k2 : HasSolution' 2 := by
  unfold HasSolution' AllProductsCongruentOne' IsValidBoundary' intervalProd'
  exact ⟨11, by decide, [3, 5, 8],
    ⟨⟨by decide, by decide⟩,
     fun i => by fin_cases i <;> native_decide⟩⟩

-- Test: Can we prove HasSolution' 3?
theorem test_k3 : HasSolution' 3 := by
  unfold HasSolution' AllProductsCongruentOne' IsValidBoundary' intervalProd'
  exact ⟨17, by decide, [2, 6, 12, 16],
    ⟨⟨by decide, by decide⟩,
     fun i => by fin_cases i <;> native_decide⟩⟩

-- Test Wilson's theorem as stated in the file
theorem test_wilson_11 : (Finset.Ico 1 11).prod id % 11 = 11 - 1 := by native_decide
theorem test_wilson_17 : (Finset.Ico 1 17).prod id % 17 = 17 - 1 := by native_decide
