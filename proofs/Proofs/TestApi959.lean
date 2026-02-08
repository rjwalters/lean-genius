import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sup
import Mathlib.Tactic

-- Test: sup of erased subset ≤ sup of original (ℕ with ⊥ = 0)
example (S : Finset ℕ) (a : ℕ) : (S.erase a).sup id ≤ S.sup id := by
  apply Finset.sup_mono (Finset.erase_subset a S)

#check @Finset.sup_mono
