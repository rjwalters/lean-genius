import Mathlib

-- Test what APIs are available

-- Test strong induction pattern
#check @Nat.strongRecOn
-- #check @Nat.strong_induction_on  -- might be renamed

-- Test summability
#check @Summable.of_norm_bounded_eventually
#check @Real.summable_pow_div_factorial
#check @NormedSpace.exp_eq_tsum

-- Test tsum ops
#check @hasSum_iff_hasSum_compl
-- #check @Finset.hasSum_compl_iff

-- Test filter
#check @Filter.Eventually.of_forall

-- Test numDerangements recurrence
#check @numDerangements_add_two

-- Test ext
#check @funext
#check @tsum_congr
