import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic

open Filter Finset

-- Test: does atTop, Real.sqrt, Real.log work?
#check @Filter.atTop ℕ _
#check Real.sqrt
#check Real.log
#check @Filter.Eventually ℕ
