-- Test API availability for Erdős #312
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics

-- Check if harmonic series divergence is available
#check Real.tendsto_sum_range_one_div_nat_succ_atTop
-- Check exp asymptotics
#check Real.exp_pos
#check Real.add_one_le_exp
#check Real.exp_ge_one_add_of_nonneg
-- Check general asymptotic tools
#check Asymptotics.IsLittleO
#check Asymptotics.isLittleO_iff
-- Check Filter tools
#check Filter.Tendsto
#check Filter.atTop
-- Check exp neg
#check Real.exp_neg
#check Real.exp_lt_one_of_neg
-- Polynomial growth vs exponential decay
#check isLittleO_pow_exp_atTop
