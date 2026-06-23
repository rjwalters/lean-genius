import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic

-- Test: factorial computation
#eval Nat.factorial 3  -- should be 6
#eval Nat.factorial 4  -- should be 24
#eval Nat.factorial 5  -- should be 120

-- Test: can we enumerate divisor pairs?
-- For factorizationMax, we need to find all ways to write n! as
-- a product of strictly increasing integers all > n.

-- Simple approach: for small n, enumerate all factorizations
-- by finding all divisors of n! that are > n

-- Test Finset.filter availability
#check @Finset.filter

-- Test: divisors
#check Nat.divisors

-- For n=3: 3! = 6, divisors of 6 that are > 3: {6}
#eval (Nat.divisors 6).filter (· > 3)  -- should be {6}

-- For n=5: 5! = 120, divisors of 120 that are > 5
#eval (Nat.divisors 120).filter (· > 5)  -- factors > 5

-- Check what we need for Finset operations
#check Finset.min'
#check Finset.Nonempty
