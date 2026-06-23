import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

-- Test what APIs are available

-- Test strong induction pattern
#check @Nat.strong_rec_on
-- #check @Nat.strong_induction_on  -- might be renamed

-- Test summability
#check @Summable.of_norm_bounded_eventually
#check @summable_pow_div_factorial
#check @NormedSpace.exp_eq_tsum

-- Test tsum ops
#check @hasSum_compl_iff
-- #check @Finset.hasSum_compl_iff

-- Test filter
#check @Filter.eventually_of_forall

-- Test numDerangements recurrence
#check @numDerangements_add_two

-- Test ext
#check @funext
#check @tsum_congr
