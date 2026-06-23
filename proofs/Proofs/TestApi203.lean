-- Test API availability for erdos-203 covering system proof
import Mathlib

-- Test: Nat.Prime.dvd_of_dvd_pow
#check Nat.Prime.dvd_of_dvd_pow

-- Test: ZMod basics
#check ZMod.val_natCast
#check @ZMod.natCast_zmod_eq_zero_iff_dvd

-- Test: Nat.pow_mod
#check Nat.pow_mod

-- Test: divisibility from mod
example : 3 ∣ (78558 : ℕ) := by decide
example : ¬ Nat.Prime 78558 := by decide

-- Test: periodic divisibility
-- If n ≡ 0 (mod 2), then 3 | 78557 * 2^n + 1
-- Key: 78557 ≡ 2 (mod 3), 2^(2k) ≡ 1 (mod 3)
-- So 78557 * 2^(2k) + 1 ≡ 2 * 1 + 1 ≡ 0 (mod 3)

-- Test: Nat.dvd_of_mod_eq_zero
#check Nat.dvd_of_mod_eq_zero

-- Test: pow pattern mod
example : (2 ^ 2) % 3 = 1 := by native_decide
example : (78557 * 1 + 1) % 3 = 0 := by native_decide

-- Test: if we can prove periodic divisibility via Nat.rec on the modular structure
-- Approach: show 2^n % p depends only on n % ord_p(2)
-- Then check all residues in the covering

-- Test: ZMod approach
example : (78557 : ZMod 3) * 1 + 1 = 0 := by decide
example : (2 : ZMod 3) ^ 2 = 1 := by decide

-- Can we do the full thing with omega/decide?
-- For k even: show 3 | 78557 * 2^k + 1
-- Need: 2^k ≡ 1 (mod 3) when k is even

-- Approach: use ZMod.pow_card_sub_one_eq_one or manual induction
#check ZMod.pow_card_sub_one_eq_one

-- Key theorem: a^(orderOf a) = 1 in any group
#check pow_orderOf_eq_one

-- orderOf (2 : ZMod 3) should be 2
-- Then 2^(2*j) = (2^2)^j = 1^j = 1 in ZMod 3

-- Test Nat approach: (a^m) % n only depends on a % n and m
-- And for periodic: (a^(p*q+r)) % n = ((a^p)^q * a^r) % n
