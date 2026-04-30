/-
  Aristotle targets for Erdos820Problem
  Routine supporting lemmas for automated proof search.
  See Proofs/Stubs/Erdos820Problem.lean for the main formalization.

  These lemmas provide building blocks for GCD of exponential sequences:
  - Basic properties of gcd(k^n - 1, l^n - 1)
  - GCD divisibility via modular arithmetic
  - Arithmetic about areNCoprime (independence of multiplicative orders)
  - Concrete small-case computations for verification
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace Erdos820.Aristotle

open Nat

/-
  ## Section 1: Symmetry and Basic GCD Properties

  gcd(k^n - 1, l^n - 1) is symmetric in k, l.
-/

-- gcd is symmetric
theorem gcd_pow_symm (k l n : ℕ) :
    Nat.gcd (k^n - 1) (l^n - 1) = Nat.gcd (l^n - 1) (k^n - 1) :=
  Nat.gcd_comm _ _

-- gcd(a, b) divides a
theorem gcd_dvd_first (k l n : ℕ) :
    Nat.gcd (k^n - 1) (l^n - 1) ∣ (k^n - 1) :=
  Nat.gcd_dvd_left _ _

-- gcd(a, b) divides b
theorem gcd_dvd_second (k l n : ℕ) :
    Nat.gcd (k^n - 1) (l^n - 1) ∣ (l^n - 1) :=
  Nat.gcd_dvd_right _ _

-- gcd(k^n - 1, k^n - 1) = k^n - 1
theorem gcd_pow_eq (k n : ℕ) : Nat.gcd (k^n - 1) (k^n - 1) = k^n - 1 :=
  Nat.gcd_self _

-- gcd(1^n - 1, l^n - 1) = l^n - 1 (since 1^n - 1 = 0)
theorem gcd_one_base (l n : ℕ) : Nat.gcd (1^n - 1) (l^n - 1) = l^n - 1 := by
  simp [Nat.gcd_zero_left]

-- k^n ≥ 1 when k ≥ 1
theorem pow_ge_one (k n : ℕ) (hk : k ≥ 1) : k^n ≥ 1 :=
  Nat.one_le_pow _ _ hk

/-
  ## Section 2: Coprimality and gcd = 1

  The condition gcd(k^n - 1, l^n - 1) = 1.
-/

-- gcd(a, b) = 1 iff a and b are Nat.Coprime
theorem gcd_one_iff_coprime (a b : ℕ) : Nat.gcd a b = 1 ↔ Nat.Coprime a b :=
  Iff.rfl

-- gcd(1, b) = 1
theorem gcd_one_left (b : ℕ) : Nat.gcd 1 b = 1 :=
  Nat.gcd_one_left b

-- gcd(a, 1) = 1
theorem gcd_one_right (a : ℕ) : Nat.gcd a 1 = 1 :=
  Nat.gcd_one_right a

-- gcd = 1 is symmetric
theorem coprime_symm (k l n : ℕ)
    (h : Nat.gcd (k^n - 1) (l^n - 1) = 1) :
    Nat.gcd (l^n - 1) (k^n - 1) = 1 := by
  rwa [Nat.gcd_comm]

-- If gcd(k^n - 1, l^n - 1) > 1, then gcd ≥ 2
theorem gcd_ge_two_of_ne_one (k l n : ℕ)
    (h : Nat.gcd (k^n - 1) (l^n - 1) ≠ 1) :
    Nat.gcd (k^n - 1) (l^n - 1) ≥ 2 := by
  omega

/-
  ## Section 3: Prime Divisibility of GCDs

  If prime p divides gcd(k^n-1, l^n-1), it divides both factors.
-/

-- If prime p | gcd(a, b), then p | a
theorem prime_dvd_gcd_dvd_left {p a b : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.gcd a b) : p ∣ a :=
  dvd_trans h (Nat.gcd_dvd_left a b)

-- If prime p | gcd(a, b), then p | b
theorem prime_dvd_gcd_dvd_right {p a b : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.gcd a b) : p ∣ b :=
  dvd_trans h (Nat.gcd_dvd_right a b)

-- p | gcd(a, b) iff p | a and p | b (for any positive p)
theorem dvd_gcd_iff (p a b : ℕ) :
    p ∣ Nat.gcd a b ↔ p ∣ a ∧ p ∣ b := by
  constructor
  · intro h
    exact ⟨dvd_trans h (Nat.gcd_dvd_left a b), dvd_trans h (Nat.gcd_dvd_right a b)⟩
  · intro ⟨ha, hb⟩
    exact Nat.dvd_gcd ha hb

-- If p is prime and p | gcd(k^n - 1, l^n - 1), then k^n ≡ 1 (mod p)
theorem prime_dvd_gcd_pow_cong_left {p k l n : ℕ} (hp : p.Prime) (hk : k ≥ 1)
    (h : p ∣ Nat.gcd (k^n - 1) (l^n - 1)) :
    k^n ≡ 1 [MOD p] := by
  have hkn : k^n ≥ 1 := Nat.one_le_pow _ _ hk
  have hdvd : p ∣ k^n - 1 := dvd_trans h (Nat.gcd_dvd_left _ _)
  exact (Nat.modEq_iff_dvd' hkn).mpr hdvd

-- If p is prime and p | gcd(k^n - 1, l^n - 1), then l^n ≡ 1 (mod p)
theorem prime_dvd_gcd_pow_cong_right {p k l n : ℕ} (hp : p.Prime) (hl : l ≥ 1)
    (h : p ∣ Nat.gcd (k^n - 1) (l^n - 1)) :
    l^n ≡ 1 [MOD p] := by
  have hln : l^n ≥ 1 := Nat.one_le_pow _ _ hl
  have hdvd : p ∣ l^n - 1 := dvd_trans h (Nat.gcd_dvd_right _ _)
  exact (Nat.modEq_iff_dvd' hln).mpr hdvd

-- If p | gcd(k^n-1, l^n-1), there exists d | n with k^d ≡ 1 [MOD p] and l^d ≡ 1 [MOD p].
-- Proof: take d = n; k^n ≡ 1 [MOD p] from p | k^n-1 (via gcd_dvd_left), similarly for l.
theorem gcd_characterization (k l n p : ℕ) (hp : Nat.Prime p) :
    p ∣ Nat.gcd (k^n - 1) (l^n - 1) →
    ∃ d : ℕ, d ∣ n ∧ (k^d ≡ 1 [MOD p]) ∧ (l^d ≡ 1 [MOD p]) := by
  sorry

/-
  ## Section 4: Concrete GCD Computations for Small n

  Verifying specific cases that H(n) = 3 (i.e., gcd(2^n - 1, 3^n - 1) = 1).
-/

-- n = 1: gcd(2^1 - 1, 3^1 - 1) = gcd(1, 2) = 1
theorem gcd_2_3_n1 : Nat.gcd (2^1 - 1) (3^1 - 1) = 1 := by norm_num

-- n = 2: gcd(2^2 - 1, 3^2 - 1) = gcd(3, 8) = 1
theorem gcd_2_3_n2 : Nat.gcd (2^2 - 1) (3^2 - 1) = 1 := by norm_num

-- n = 3: gcd(2^3 - 1, 3^3 - 1) = gcd(7, 26) = 1
theorem gcd_2_3_n3 : Nat.gcd (2^3 - 1) (3^3 - 1) = 1 := by norm_num

-- n = 4: gcd(2^4 - 1, 3^4 - 1) = gcd(15, 80) = 5 ≠ 1
theorem gcd_2_3_n4 : Nat.gcd (2^4 - 1) (3^4 - 1) = 5 := by norm_num

-- n = 5: gcd(2^5 - 1, 3^5 - 1) = gcd(31, 242) = 1
theorem gcd_2_3_n5 : Nat.gcd (2^5 - 1) (3^5 - 1) = 1 := by norm_num

-- n = 7: gcd(2^7 - 1, 3^7 - 1) = gcd(127, 2186) = 1
theorem gcd_2_3_n7 : Nat.gcd (2^7 - 1) (3^7 - 1) = 1 := by norm_num

-- n = 4 is NOT coprime (witnesses that H(4) > 3)
theorem not_coprime_n4 : Nat.gcd (2^4 - 1) (3^4 - 1) ≠ 1 := by norm_num

/-
  ## Section 5: Power Ordering Facts

  Useful for bounding H(n).
-/

-- 2^n < 3^n for n ≥ 1
theorem two_pow_lt_three_pow (n : ℕ) (hn : n ≥ 1) : 2^n < 3^n := by
  apply Nat.pow_lt_pow_left (by norm_num) (by omega)

-- For k ≥ 2, k^n ≥ 2 for n ≥ 1
theorem pow_ge_two (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ 1) : k^n ≥ 2 := by
  calc k^n ≥ k^1 := Nat.pow_le_pow_right (by omega) hn
    _ = k := pow_one k
    _ ≥ 2 := hk

-- k^n - 1 ≥ 1 when k ≥ 2 and n ≥ 1
theorem pow_sub_one_pos (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ 1) : k^n - 1 ≥ 1 := by
  have := pow_ge_two k n hk hn
  omega

-- k^n is strictly increasing in n for k ≥ 2
theorem pow_strict_mono (k n m : ℕ) (hk : k ≥ 2) (h : n < m) : k^n < k^m :=
  Nat.pow_lt_pow_right (by omega) h

-- gcd(k^n - 1, l^n - 1) = 0 iff k = 1 and l = 1 (since both = 0)
theorem gcd_pow_zero_iff (k l n : ℕ) (hn : n ≥ 1) :
    Nat.gcd (k^n - 1) (l^n - 1) = 0 ↔ k = 1 ∧ l = 1 := by
  sorry

end Erdos820.Aristotle
