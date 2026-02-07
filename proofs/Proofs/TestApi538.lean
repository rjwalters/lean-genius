-- Test API availability for Erdos 538
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- Test basic Finset operations
#check Finset.sum_empty
#check Finset.sum_nonneg
#check Finset.sum_le_sum
#check Finset.filter_subset
#check Finset.card_filter_le
#check Finset.sum_le_sum_of_subset_of_nonneg

-- Test real number ops
#check div_nonneg
#check one_div_nonneg
