-- Test API availability for erdos-196 proof work
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

-- Test that basic tools work
example (a b : ℕ) (h : a % 2 ≠ 1) : a % 2 = 0 := by omega
example (a b c d : ℕ) (h1 : b - a = c - b) (h2 : c - b = d - c) (h3 : a < b) : a < d := by omega

-- Test Equiv basics
#check Equiv
#check Function.Injective
#check StrictMono
