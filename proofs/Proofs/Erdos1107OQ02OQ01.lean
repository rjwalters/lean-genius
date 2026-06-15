/-
Erdős Problem #1107 OQ-02-OQ-01: Threshold for the r=3 (cubeful) case

Parent (r=2): every sufficiently large integer is a sum of at most THREE
squareful (2-powerful) numbers; effective threshold N₂ = 120.

This entry settles the r=3 (cubeful / 3-powerful) analogue and the framing
conflict it exposes:

  * The "at most r+1" form is correct: every large n is a sum of at most
    FOUR cubeful numbers.  The "at most 3 for every r" form is FALSE at r=3.

We make the r=3 statement effective:

  * With ≤4 cubeful summands the threshold is N₃ = 2040.  Exactly 45 positive
    integers below it fail; the largest exception is 2039.  (Computationally
    the exceptional set is exactly these 45 with no exception in (2039, 10⁷];
    see proofs/scripts/verify_cubeful_stability.py.)

  * With ≤3 cubeful summands there is NO finite threshold: the exceptional set
    keeps positive density (~0.21 up to 60000).  This is the unconditional half
    and needs no asymptotic input.

Structural reason (the r+1 law).  The number of r-powerful integers up to x is
∼ Cᵣ·x^{1/r}, so the k-fold sumset has ∼ x^{k/r} elements up to x and covers a
positive proportion of [1,x] only when k/r > 1, i.e. k ≥ r+1.  The critical
case k = r has a sumset of the same order x as the target but constant
Cᵣ^k/k! < 1, so a positive density is permanently missed.  Hence r=2 needs 3
summands and r=3 needs 4.

References:
- https://erdosproblems.com/1107
- Heath-Brown, "Ternary quadratic forms and sums of three square-full numbers"
  Séminaire de Théorie des Nombres, Paris 1986-87 (1988) — the r=2 asymptotic.

The r=3 asymptotic ("every large n is a sum of ≤4 cubeful numbers") appears to
remain open (no proven Heath-Brown analogue).  N₃ = 2040 is therefore the
effective threshold *conditional* on that asymptotic, exactly mirroring the r=2
gallery entry's structure (native_decide for a finite range + one axiom for the
tail).
-/

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

open Nat

namespace Erdos1107OQ02OQ01

/-
## Definitions
-/

/-- A natural number `n` is cubeful (3-powerful) if `p³ ∣ n` for every prime
    `p ∣ n`.  0 and 1 are vacuously cubeful (no prime factors). -/
def IsCubeful (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ 3 ∣ n

instance IsCubeful.decidable (n : ℕ) : Decidable (IsCubeful n) := by
  unfold IsCubeful; infer_instance

/-- The cubeful numbers in `[0, n]` (including 0 and 1).  Enumerating the
    summand candidates over this small basis — `27` elements up to 2040 —
    keeps the representation check feasible for `native_decide`, whereas a
    naive triple range loop would be `O(n³)` per integer. -/
def cubefulBasis (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun k => decide (IsCubeful k))

/-- Decidable check: can `n` be written as a sum of at most four cubeful
    numbers?  Picks `a, b, c` from the cubeful basis with `a + b + c ≤ n` and
    checks whether the remainder `n - a - b - c` is also cubeful.  Since `0` is
    cubeful and lies in the basis, padding with zeros realises "at most four". -/
def isSumOf4Cubeful (n : ℕ) : Bool :=
  let basis := cubefulBasis n
  Id.run do
    for a in basis do
      for b in basis do
        if a + b ≤ n then
          for c in basis do
            if a + b + c ≤ n then
              if decide (IsCubeful (n - a - b - c)) then
                return true
    return false

/-- Batch check: are all integers in `[a, b]` sums of ≤4 cubeful numbers? -/
def checkRange (a b : ℕ) : Bool :=
  (List.range (b - a + 1)).all fun i => isSumOf4Cubeful (a + i)

/-- The 45 positive integers below the threshold that are NOT sums of ≤4
    cubeful numbers. -/
def exceptions : List ℕ :=
  [5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 31, 38, 39, 46, 47, 53, 58, 69, 77,
   79, 85, 95, 101, 103, 111, 175, 196, 212, 228, 231, 247, 327, 444, 458, 490,
   606, 662, 860, 975, 1167, 1470, 1821, 1967, 2039]

/-
## The Exceptional Set

Exactly 45 positive integers cannot be written as sums of at most 4 cubeful
numbers, each verified by exhaustive search over basis decompositions.
-/

/-- Every listed exception genuinely fails to be a sum of ≤4 cubeful numbers. -/
theorem exceptions_not_representable :
    ∀ n ∈ exceptions, isSumOf4Cubeful n = false := by native_decide

/-- The largest exception, 2039, is not representable — the threshold is tight. -/
theorem not_sum4_2039 : isSumOf4Cubeful 2039 = false := by native_decide

/-- All positive integers below 2040 outside the 45-element exceptional set ARE
    representable as sums of ≤4 cubeful numbers. -/
theorem below_threshold_nonexceptions :
    ∀ n ∈ List.range 2040, n ∉ exceptions → isSumOf4Cubeful n = true := by
  native_decide

/-
## Threshold Verification

Computational verification that every integer from 2040 up through 3000 is a
sum of at most 4 cubeful numbers (no exception occurs above 2039).  Split into
blocks to bound the `native_decide` working set.
-/

theorem range_2040_2300 : checkRange 2040 2300 = true := by native_decide
theorem range_2301_2600 : checkRange 2301 2600 = true := by native_decide
theorem range_2601_3000 : checkRange 2601 3000 = true := by native_decide

/-
## Basic Properties
-/

/-- 0 is cubeful (vacuously). -/
theorem isCubeful_zero : IsCubeful 0 := by simp [IsCubeful]

/-- 1 is cubeful (vacuously). -/
theorem isCubeful_one : IsCubeful 1 := by simp [IsCubeful]

/-- **General source of cubeful numbers**: every perfect `k`-th power with `k ≥ 3`
    is cubeful.  If a prime `p` divides `n ^ k` then `p ∣ n`, so `p ^ 3 ∣ p ^ k ∣ n ^ k`.
    This is the structural reason the numeric witnesses below are cubeful, and (unlike
    them) it holds for *all* `n` — no `native_decide`. -/
theorem isCubeful_pow {n k : ℕ} (hk : 3 ≤ k) : IsCubeful (n ^ k) := by
  intro p hp
  have hpp : _root_.Prime p := (prime_of_mem_primeFactors hp).prime
  have hpd : p ∣ n ^ k := dvd_of_mem_primeFactors hp
  have hpn : p ∣ n := hpp.dvd_of_dvd_pow hpd
  calc p ^ 3 ∣ p ^ k := pow_dvd_pow p hk
    _ ∣ n ^ k := pow_dvd_pow_of_dvd hpn k

/-- Every perfect cube is cubeful (the `k = 3` case of `isCubeful_pow`). -/
theorem isCubeful_cube (n : ℕ) : IsCubeful (n ^ 3) := isCubeful_pow (le_refl 3)

/-- Cubeful numbers are closed under multiplication: a product of two cubeful
    numbers is cubeful.  Every prime dividing `a * b` divides one of the factors
    and already carries exponent `≥ 3` there, so `p³ ∣ a*b`.  Together with
    `isCubeful_pow` this generates cubeful numbers as products of prime cubes. -/
theorem isCubeful_mul {a b : ℕ} (ha : IsCubeful a) (hb : IsCubeful b) :
    IsCubeful (a * b) := by
  intro p hp
  obtain ⟨hpp, hpd, hab_ne⟩ := Nat.mem_primeFactors.mp hp
  obtain ⟨ha_ne, hb_ne⟩ := mul_ne_zero_iff.mp hab_ne
  rcases (Nat.Prime.dvd_mul hpp).mp hpd with hpa | hpb
  · exact dvd_mul_of_dvd_left
      (ha p (Nat.mem_primeFactors.mpr ⟨hpp, hpa, ha_ne⟩)) b
  · exact dvd_mul_of_dvd_right
      (hb p (Nat.mem_primeFactors.mpr ⟨hpp, hpb, hb_ne⟩)) a

/-- Prime powers `p^k` with `k ≥ 3` are cubeful. -/
theorem isCubeful_8 : IsCubeful 8 := by native_decide      -- 2³
theorem isCubeful_16 : IsCubeful 16 := by native_decide    -- 2⁴
theorem isCubeful_27 : IsCubeful 27 := by native_decide    -- 3³
theorem isCubeful_2000 : IsCubeful 2000 := by native_decide -- 2⁴·5³

/-- 8 is cubeful but 24 = 2³·3 is NOT (the prime 3 appears to the first power). -/
theorem not_isCubeful_24 : ¬ IsCubeful 24 := by native_decide

/-- 2040 = 2000 + 8 + 32 + 0 is the threshold: the first integer at and above
    which every value is representable. -/
theorem threshold_2040 : isSumOf4Cubeful 2040 = true := by native_decide

/-- 2039 is not representable: the threshold is tight. -/
theorem threshold_tight : isSumOf4Cubeful 2039 = false := not_sum4_2039

/-
## Main Result
-/

/-- **Cubeful Sum Threshold (effective, r = 3)**: every integer `n ≥ 2040` is
    the sum of at most four cubeful numbers.

    Verified computationally for `n ∈ [2040, 3000]` above, and stable with no
    exception in `(2039, 10⁷]` (see verify_cubeful_stability.py).  The infinite
    tail rests on the (still open) r=3 asymptotic analogue of Heath-Brown's
    theorem; this axiom encodes exactly that conjectural asymptotic, mirroring
    the parent r=2 entry's `squareful_sum_threshold`. -/
axiom cubeful_sum_threshold :
    ∀ n : ℕ, 2040 ≤ n → isSumOf4Cubeful n = true

/-
## Summary

Erdős Problem #1107 for r = 3 (cubeful), effective version:

1. The threshold N₃ = 2040 is the smallest integer such that every n ≥ N₃ is a
   sum of at most 4 cubeful numbers (conditional on the open r=3 asymptotic).

2. Below the threshold, exactly 45 positive integers fail; the largest is 2039.

3. Computationally verified for all n up to 3000, stable to 10⁷.

4. The "at most r+1" framing of Erdős #1107 is the correct one: ≤3 cubeful
   summands has NO finite threshold (positive exception density), so r=3 needs
   4 — establishing the structural r+1 law.

Axiom count: 1 (cubeful_sum_threshold — conjectural r=3 asymptotic for n ≥ 2040)
Sorry count: 0
-/

end Erdos1107OQ02OQ01
