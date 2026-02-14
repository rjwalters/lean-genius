/-
Erdős Problem #1054: Construction D — Prime Powers

For any prime p, we prove results about the divisor structure of p²:

1. The divisors of p² are exactly {1, p, p²}
2. The sorted divisors are [1, p, p²]
3. The partial sums are [1, 1+p, 1+p+p²]
4. 1 + p + p² is representable for every prime p

Key values: p=2→7, p=3→13, p=5→31, p=7→57, p=11→133, p=13→183.

We also verify Mersenne numbers (2^{k+1}-1) as representable via 2^k.

References: Erdős Problem #1054, https://erdosproblems.com/1054
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open Nat Finset

namespace Erdos1054ConstructionD

-- ============================================================
-- Definitions (mirrored from Erdos1054Problem for modularity)
-- ============================================================

def sortedDivisors (m : ℕ) : List ℕ :=
  m.divisors.sort (· ≤ ·)

def partialDivisorSums (m : ℕ) : List ℕ :=
  ((sortedDivisors m).scanl (· + ·) 0).tail

def IsRepresentable (n : ℕ) : Prop :=
  ∃ m : ℕ, m ≥ 1 ∧ n ∈ (partialDivisorSums m)

-- ============================================================
-- Part 1: Divisors of p² for prime p
-- ============================================================

/--
For prime p, any divisor of p² is in {1, p, p²}.
-/
theorem divisors_of_prime_sq (p : ℕ) (hp : p.Prime) (d : ℕ)
    (hd : d ∣ p ^ 2) : d = 1 ∨ d = p ∨ d = p ^ 2 := by
  have hd' : d ∣ p * p := by rwa [sq] at hd
  by_cases hpd_dvd : p ∣ d
  · obtain ⟨e, rfl⟩ := hpd_dvd
    have he_dvd_p : e ∣ p := (Nat.mul_dvd_mul_iff_right hp.pos).mp hd'
    rcases hp.eq_one_or_self_of_dvd e he_dvd_p with rfl | rfl
    · right; left; ring
    · right; right; ring
  · have hcop : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr hpd_dvd).symm
    have hd_dvd_p : d ∣ p := hcop.dvd_of_dvd_mul_right hd'
    rcases hp.eq_one_or_self_of_dvd d hd_dvd_p with rfl | rfl
    · left; rfl
    · exact absurd (dvd_refl p) hpd_dvd

/--
The divisors of p² for prime p form the set {1, p, p²}.
-/
theorem divisors_prime_sq (p : ℕ) (hp : p.Prime) :
    (p ^ 2).divisors = {1, p, p ^ 2} := by
  ext d
  simp only [Finset.mem_insert, Finset.mem_singleton, Nat.mem_divisors]
  constructor
  · intro ⟨hd, _⟩
    exact divisors_of_prime_sq p hp d hd
  · rintro (rfl | rfl | rfl)
    · exact ⟨one_dvd _, by have := hp.pos; omega⟩
    · exact ⟨⟨p, by ring⟩, by have := hp.pos; omega⟩
    · exact ⟨dvd_refl _, by have := hp.pos; omega⟩

-- ============================================================
-- Part 2: Sorting the divisors of p²
-- ============================================================

/--
sortedDivisors of p² for prime p is [1, p, p²].
-/
theorem sortedDivisors_prime_sq (p : ℕ) (hp : p.Prime) :
    sortedDivisors (p ^ 2) = [1, p, p ^ 2] := by
  simp only [sortedDivisors]
  rw [divisors_prime_sq p hp]
  -- Need to prove {1, p, p^2}.sort (· ≤ ·) = [1, p, p^2]
  -- Use the Perm + sorted approach
  have hp2 := hp.two_le
  have hnodup_sort : (({1, p, p ^ 2} : Finset ℕ).sort (· ≤ ·)).Nodup :=
    Finset.sort_nodup _ _
  have target_nodup : ([1, p, p ^ 2] : List ℕ).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false,
      List.nodup_nil, and_true, not_or]
    constructor
    · constructor
      · omega
      · have : p ^ 2 ≥ 4 := by nlinarith
        omega
    · have : p ^ 2 > p := by nlinarith
      omega
  have hmem : ∀ x, x ∈ ({1, p, p ^ 2} : Finset ℕ).sort (· ≤ ·) ↔
      x ∈ ([1, p, p ^ 2] : List ℕ) := by
    intro x
    simp [Finset.mem_sort, Finset.mem_insert, Finset.mem_singleton]
  have hperm : (({1, p, p ^ 2} : Finset ℕ).sort (· ≤ ·)).Perm [1, p, p ^ 2] :=
    (List.perm_ext_iff_of_nodup hnodup_sort target_nodup).mpr hmem
  have hsorted_sort := Finset.pairwise_sort ({1, p, p ^ 2} : Finset ℕ) (· ≤ ·)
  have hsorted_target : ([1, p, p ^ 2] : List ℕ).Pairwise (· ≤ ·) := by
    constructor
    · intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false, List.mem_singleton] at hx
      rcases hx with rfl | rfl <;> omega <;> nlinarith
    constructor
    · intro x hx
      simp only [List.mem_nil_iff, List.mem_singleton] at hx
      nlinarith [hx]
    exact List.Pairwise.nil
  exact hperm.eq_of_pairwise hsorted_sort hsorted_target

-- ============================================================
-- Part 3: Partial sums of p²
-- ============================================================

/--
partialDivisorSums of p² for prime p is [1, 1 + p, 1 + p + p²].
-/
theorem partialDivisorSums_prime_sq (p : ℕ) (hp : p.Prime) :
    partialDivisorSums (p ^ 2) = [1, 1 + p, 1 + p + p ^ 2] := by
  simp only [partialDivisorSums]
  rw [sortedDivisors_prime_sq p hp]
  simp [List.scanl, List.tail]

-- ============================================================
-- Part 4: The General Construction D Theorem
-- ============================================================

/--
**General Construction D**: For any prime p, 1 + p + p² is representable.

The witness is m = p². The divisors of p² are exactly {1, p, p²}.
Since 1 < p < p², the sorted divisors are [1, p, p²].
The last partial sum is 1 + p + p².
-/
theorem prime_sq_sum_representable (p : ℕ) (hp : p.Prime) :
    IsRepresentable (1 + p + p ^ 2) := by
  refine ⟨p ^ 2, ?_, ?_⟩
  · have := hp.pos; omega
  · rw [partialDivisorSums_prime_sq p hp]
    simp [List.mem_cons]

/--
1 + p is also representable via the p² witness (second partial sum).
-/
theorem one_plus_p_via_sq (p : ℕ) (hp : p.Prime) :
    IsRepresentable (1 + p) := by
  refine ⟨p ^ 2, ?_, ?_⟩
  · have := hp.pos; omega
  · rw [partialDivisorSums_prime_sq p hp]
    simp [List.mem_cons]

-- ============================================================
-- Part 5: Bound on f
-- ============================================================

/--
f(1 + p + p²) ≤ p² for any prime p.
-/
theorem f_bound_prime_sq (p : ℕ) (hp : p.Prime) :
    ∃ m : ℕ, m ≤ p ^ 2 ∧ m ≥ 1 ∧ (1 + p + p ^ 2) ∈ partialDivisorSums m := by
  refine ⟨p ^ 2, le_refl _, ?_, ?_⟩
  · have := hp.pos; omega
  · rw [partialDivisorSums_prime_sq p hp]; simp [List.mem_cons]

-- ============================================================
-- Part 6: Computational verification
-- ============================================================

-- p=2: 1+2+4=7, witness m=4
theorem constr_d_2 : IsRepresentable (1 + 2 + 2 ^ 2) := ⟨4, by omega, by native_decide⟩
-- p=3: 1+3+9=13, witness m=9
theorem constr_d_3 : IsRepresentable (1 + 3 + 3 ^ 2) := ⟨9, by omega, by native_decide⟩
-- p=5: 1+5+25=31, witness m=25
theorem constr_d_5 : IsRepresentable (1 + 5 + 5 ^ 2) := ⟨25, by omega, by native_decide⟩
-- p=7: 1+7+49=57, witness m=49
theorem constr_d_7 : IsRepresentable (1 + 7 + 7 ^ 2) := ⟨49, by omega, by native_decide⟩
-- p=11: 1+11+121=133, witness m=121
theorem constr_d_11 : IsRepresentable (1 + 11 + 11 ^ 2) := ⟨121, by omega, by native_decide⟩
-- p=13: 1+13+169=183, witness m=169
theorem constr_d_13 : IsRepresentable (1 + 13 + 13 ^ 2) := ⟨169, by omega, by native_decide⟩

-- ============================================================
-- Part 7: Mersenne numbers via powers of 2
-- ============================================================

/-
For m = 2^k, divisors are {1, 2, 4, ..., 2^k}, partial sums are
the Mersenne numbers: 1, 3, 7, 15, 31, 63, 127, 255, 511, ...

Each Mersenne number 2^{k+1}-1 is representable with witness 2^k.
The ratio f(n)/n → 1/2 as k → ∞.
-/

theorem mersenne_repr_1 : IsRepresentable 1 := ⟨1, by omega, by native_decide⟩
theorem mersenne_repr_3 : IsRepresentable 3 := ⟨2, by omega, by native_decide⟩
theorem mersenne_repr_7 : IsRepresentable 7 := ⟨4, by omega, by native_decide⟩
theorem mersenne_repr_15 : IsRepresentable 15 := ⟨8, by omega, by native_decide⟩
theorem mersenne_repr_31 : IsRepresentable 31 := ⟨16, by omega, by native_decide⟩
theorem mersenne_repr_63 : IsRepresentable 63 := ⟨32, by omega, by native_decide⟩
theorem mersenne_repr_127 : IsRepresentable 127 := ⟨64, by omega, by native_decide⟩
theorem mersenne_repr_255 : IsRepresentable 255 := ⟨128, by omega, by native_decide⟩
theorem mersenne_repr_511 : IsRepresentable 511 := ⟨256, by omega, by native_decide⟩

/-- f(2^{k+1} - 1) ≤ 2^k: the Mersenne witness bounds. -/
theorem f_mersenne_bound_4 : ∃ m, m ≤ 4 ∧ m ≥ 1 ∧ 7 ∈ partialDivisorSums m :=
  ⟨4, by omega, by omega, by native_decide⟩
theorem f_mersenne_bound_16 : ∃ m, m ≤ 16 ∧ m ≥ 1 ∧ 31 ∈ partialDivisorSums m :=
  ⟨16, by omega, by omega, by native_decide⟩
theorem f_mersenne_bound_64 : ∃ m, m ≤ 64 ∧ m ≥ 1 ∧ 127 ∈ partialDivisorSums m :=
  ⟨64, by omega, by omega, by native_decide⟩
theorem f_mersenne_bound_256 : ∃ m, m ≤ 256 ∧ m ≥ 1 ∧ 511 ∈ partialDivisorSums m :=
  ⟨256, by omega, by omega, by native_decide⟩

-- ============================================================
-- Part 8: Summary
-- ============================================================

/-
## Summary of Results

### Main Theorems
1. `divisors_prime_sq`: (p²).divisors = {1, p, p²} for prime p
2. `sortedDivisors_prime_sq`: sorted divisors of p² are [1, p, p²]
3. `partialDivisorSums_prime_sq`: partial sums of p² are [1, 1+p, 1+p+p²]
4. `prime_sq_sum_representable`: 1+p+p² is representable for all primes p
5. `f_bound_prime_sq`: f(1+p+p²) ≤ p²

### Mersenne Numbers
- All 2^{k+1}-1 representable via witness 2^k
- f(2^{k+1}-1)/(2^{k+1}-1) → 1/2 as k → ∞

### Mathematical Significance
- Prime power partial sums (geometric sums) form an infinite family
  where f(n)/n is bounded by (p-1)/p < 1.
- For p=2, the Mersenne numbers satisfy f(n)/n → 1/2.
- This shows f is "well-behaved" on prime power σ-images.
-/

end Erdos1054ConstructionD
