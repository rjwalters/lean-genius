/-
  Aristotle targets for Erdős Problem #876 (Sum-Free Sets and Gap Growth)
  Routine supporting lemmas for automated proof search.
  See Erdos876Problem.lean for the main formalization.

  The main sorry in Erdos876Problem.lean is:
  - powers_of_two_sumfree: IsSumFreeErdos {n | ∃ k : ℕ, n = 2^k}

  Proof strategy: no power of 2 equals a sum of 2+ distinct smaller
  powers of 2, because the sum of all powers of 2 below 2^k is 2^k - 1.

  Criteria for inclusion:
  - NOT open gap questions (ErdosQuestion876, graham_result)
  - Routine arithmetic facts about powers of 2 and Finset sums
  - No axioms, no definition sorries, no open conjectures
  - No /-! docstring sections
-/
import Mathlib

namespace Erdos876.Aristotle

open Nat Finset

/-
## Section 1: Monotonicity of 2^k — purely arithmetic, omega/simp level
-/

-- Aristotle target: 2^i < 2^j iff i < j
theorem two_pow_strictMono : StrictMono (2 ^ · : ℕ → ℕ) :=
  fun _i _j h => Nat.pow_lt_pow_right (by norm_num) h

-- Aristotle target: if 2^j < 2^k then j < k
theorem exp_lt_of_pow2_lt {j k : ℕ} (h : 2 ^ j < 2 ^ k) : j < k :=
  (Nat.pow_lt_pow_left_iff (by norm_num)).mp h

-- Aristotle target: powers of 2 are injective in the exponent
theorem two_pow_injective : Function.Injective (2 ^ · : ℕ → ℕ) :=
  fun i j h => Nat.pow_right_injective (by norm_num) h

/-
## Section 2: Geometric series — provable by induction + omega
-/

-- Aristotle target: ∑_{j < k} 2^j = 2^k - 1
theorem geom_sum_pow2 (k : ℕ) :
    (Finset.range k).sum (2 ^ ·) = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

-- Aristotle target: for k ≥ 1, the geometric partial sum is < 2^k
theorem geom_sum_lt_pow2 {k : ℕ} (hk : 0 < k) :
    (Finset.range k).sum (2 ^ ·) < 2 ^ k := by
  rw [geom_sum_pow2]
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

-- Aristotle target: any sub-range Finset has a smaller power-of-2 sum
theorem sum_pow2_subset_lt {k : ℕ} (hk : 0 < k) {E : Finset ℕ}
    (hE : E ⊆ Finset.range k) :
    E.sum (2 ^ ·) < 2 ^ k :=
  lt_of_le_of_lt (Finset.sum_le_sum_of_subset hE) (geom_sum_lt_pow2 hk)

/-
## Section 3: log₂ of powers of 2 — Mathlib lookup targets
-/

-- Aristotle target: Nat.log 2 (2^k) = k
theorem log2_pow (k : ℕ) : Nat.log 2 (2 ^ k) = k := by
  sorry

-- Aristotle target: if 2^j < 2^k then log 2 (2^j) < k
theorem log2_pow_lt {j k : ℕ} (h : 2 ^ j < 2 ^ k) :
    Nat.log 2 (2 ^ j) < k := by
  sorry

-- Aristotle target: log 2 is injective on the set of powers of 2
theorem log2_injOn_pow2 (a b : ℕ) (ha : ∃ i, a = 2 ^ i) (hb : ∃ j, b = 2 ^ j)
    (h : Nat.log 2 a = Nat.log 2 b) : a = b := by
  sorry

/-
## Section 4: Exponent image and sum rewrite — Finset manipulation targets
-/

-- Aristotle target: image of S ⊆ powers-of-2 under log 2 is ⊆ range k
-- when all elements of S are < 2^k
theorem image_log2_subset_range {k : ℕ} {S : Finset ℕ}
    (hS : ∀ n ∈ S, ∃ j, n = 2 ^ j)
    (hlt : ∀ n ∈ S, n < 2 ^ k) :
    S.image (Nat.log 2) ⊆ Finset.range k := by
  sorry

-- Aristotle target: Σ_{n ∈ S} n = Σ_{e ∈ S.image(log 2)} 2^e
-- when every n ∈ S is a power of 2
theorem sum_eq_sum_image_log2 {S : Finset ℕ} (hS : ∀ n ∈ S, ∃ k, n = 2 ^ k) :
    S.sum id = (S.image (Nat.log 2)).sum (2 ^ ·) := by
  sorry

/-
## Section 5: Main bound — consequences of Sections 2–4
-/

-- Aristotle target: a Finset of powers of 2, all < 2^k, has sum < 2^k
-- (Follows from sum_eq_sum_image_log2 + image_log2_subset_range + sum_pow2_subset_lt)
theorem sum_pow2_finset_lt {k : ℕ} (hk : 0 < k) {S : Finset ℕ}
    (hS : ∀ n ∈ S, ∃ j, n = 2 ^ j)
    (hlt : ∀ n ∈ S, n < 2 ^ k) :
    S.sum id < 2 ^ k := by
  rw [sum_eq_sum_image_log2 hS]
  exact sum_pow2_subset_lt hk (image_log2_subset_range hS hlt)

end Erdos876.Aristotle
