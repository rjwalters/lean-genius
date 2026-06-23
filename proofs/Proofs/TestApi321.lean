import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset

-- Test: Finset.sum over rationals
#check @Finset.sum ℕ ℚ _ -- should give Finset ℕ → (ℕ → ℚ) → ℚ

-- Test: subset monotonicity type
example (A : Finset ℕ) (S T : Finset ℕ) (hS : S ⊆ A) (hT : T ⊆ A) :
    S ⊆ A := hS

-- Test: Finset.sum_empty
#check @Finset.sum_empty ℕ ℚ _

-- Test: Finset.sum_singleton
#check @Finset.sum_singleton

-- Test: Rat division
example : (1 : ℚ) / 2 ≠ (1 : ℚ) / 3 := by norm_num

-- Test: Finset.subset_refl
#check @Finset.Subset.refl

-- Test: empty finset
#check (∅ : Finset ℕ)

-- Test: singleton finset
#check ({3} : Finset ℕ)

-- Test: Finset.card
#check @Finset.card ℕ

-- Test: powerset
#check @Finset.powerset ℕ

-- Test: mem_powerset
#check @Finset.mem_powerset ℕ

-- Test: Rat.div_ne_zero or similar
example (n : ℕ) (hn : n ≠ 0) : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn

-- Test: 1/a ≠ 1/b for distinct positive nats
example : (1 : ℚ) / 1 ≠ (1 : ℚ) / 2 := by norm_num
example : (1 : ℚ) / 2 ≠ (1 : ℚ) / 3 := by norm_num

-- Test: sum of singleton
example : Finset.sum {(2 : ℕ)} (fun n => (1 : ℚ) / n) = 1/2 := by simp

-- Test: Finset.filter
#check @Finset.filter

-- Test: Finset.sup for ℕ
#check @Finset.sup ℕ ℕ _
