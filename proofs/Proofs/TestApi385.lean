import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Set.Finite.Basic

-- Test: minFac APIs
#check Nat.minFac_sq_le_self
#check Nat.minFac_prime
#check Nat.minFac_dvd

-- Test: minFac_sq_le_self
example (n : ℕ) (hn : n > 1) : n.minFac ^ 2 ≤ n := by
  exact Nat.minFac_sq_le_self (by omega)

-- Test: le_sqrt API name
#check @Nat.le_sqrt'

-- Test: eventually_atTop
#check Filter.eventually_atTop
#check @Filter.Tendsto

-- Test: Set.Finite
#check Set.Finite
#check Set.Finite.subset
