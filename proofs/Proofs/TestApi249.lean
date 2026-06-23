/-
  Test API availability for Erdős #249 proof
-/
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

-- Test: Summable.of_nonneg_of_le
#check Summable.of_nonneg_of_le

-- Test: summable_geometric_of_lt_one
#check summable_geometric_of_lt_one

-- Test: tsum_le_tsum
#check tsum_le_tsum

-- Test: tsum_pos
#check tsum_pos

-- Test: Nat.totient_le
#check Nat.totient_le

-- Test: Nat.totient_one
#check Nat.totient_one

-- Test: Nat.totient_prime
#check Nat.totient_prime

-- Test: summable_of_summable_norm (for absolute convergence)
#check Summable.of_norm

-- Test for norm summable
#check summable_of_summable_norm

-- Test: summable_of_nonneg_of_le (alternative name)
#check Summable.of_nonneg_of_le

-- Test: HasSum
#check HasSum

-- Test: tsum_geometric_of_lt_one
#check tsum_geometric_of_lt_one

-- Test: Summable.mul_left
#check Summable.mul_left

-- Approach: use summable_of_sum_le or similar
-- φ(n)/2^n ≤ n/2^n ≤ (for large n) C * (3/4)^n
-- Or more directly: use summable_of_nonneg_of_le with a known bound

-- Key idea: n * r^n is summable for |r| < 1
-- Test if there's a direct lemma
#check summable_pow_mul_geometric_of_norm_lt_one

-- Test: For tsum positivity
-- Need: if Summable f, all terms nonneg, one term positive => tsum > 0
#check tsum_pos

-- Test NNReal approach
#check NNReal.summable_of_le
