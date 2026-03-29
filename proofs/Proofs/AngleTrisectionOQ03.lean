/-
  Angle Trisection OQ03: Computational Complexity of Determining Constructibility

  Extension of the angle trisection formalization exploring decidability and
  computational aspects of compass-and-straightedge constructibility.

  Key results:
  - A positive natural number divides some power of 2 iff it is a power of 2
  - Constructibility (given the minimal polynomial degree) is decidable
  - N-gon constructibility is decidable via Euler's totient
  - The decision problem reduces to O(log d) arithmetic operations

  Dependencies:
  - AngleTrisection.lean: IsConstructible definition, Wantzel's theorem
  - AngleTrisectionOQ02OQ03.lean: Gauss-Wantzel theorem, IsConstructibleNgon
-/

import Mathlib
import Proofs.AngleTrisection
import Proofs.AngleTrisectionOQ02OQ03

open AngleTrisection AngleTrisectionOQ02OQ03

namespace AngleTrisectionOQ03

/-
## Part I: Characterizing the Power-of-2 Divisibility Condition

The constructibility predicate `IsConstructible α d` reduces to checking
whether d > 0 and d divides some power of 2. We characterize the latter
condition: it holds iff d is itself a power of 2.
-/

/-- A positive divisor of 2^m is itself a power of 2. -/
theorem dvd_pow_two_is_pow_two {d m : ℕ} (hd : 0 < d) (h : d ∣ 2 ^ m) :
    ∃ k : ℕ, d = 2 ^ k := by
  induction m generalizing d with
  | zero =>
    rw [pow_zero] at h
    exact ⟨0, Nat.eq_one_of_dvd_one h⟩
  | succ m ih =>
    by_cases h2 : 2 ∣ d
    · obtain ⟨d', rfl⟩ := h2
      have hd' : 0 < d' := by omega
      have h' : d' ∣ 2 ^ m := by
        rw [pow_succ] at h
        exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp h
      obtain ⟨k, hk⟩ := ih hd' h'
      exact ⟨k + 1, by rw [hk, pow_succ]⟩
    · have hd1 : d = 1 := by
        by_contra hne
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
        have : p = 2 := by
          have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (dvd_trans hpd h)
          exact le_antisymm (Nat.le_of_dvd (by omega) hp2) hp.two_le
        exact h2 (this ▸ hpd)
      exact ⟨0, by rw [hd1, pow_zero]⟩

/-- For d > 0, d divides some power of 2 iff d is a power of 2. -/
theorem dvd_pow_two_iff_pow_two {d : ℕ} (hd : 0 < d) :
    (∃ n : ℕ, d ∣ 2 ^ n) ↔ ∃ k : ℕ, d = 2 ^ k := by
  constructor
  · rintro ⟨n, h⟩; exact dvd_pow_two_is_pow_two hd h
  · rintro ⟨k, rfl⟩; exact ⟨k, dvd_refl _⟩

/-- For d = 0, there is no n such that 0 ∣ 2^n. -/
theorem zero_not_dvd_pow_two : ¬∃ n : ℕ, 0 ∣ 2 ^ n := by
  rintro ⟨n, h⟩
  have h1 : 2 ^ n = 0 := zero_dvd_iff.mp h
  have h2 : 0 < 2 ^ n := by positivity
  omega

/-
## Part II: Prime Factor Characterization

A number divides a power of 2 iff all its prime factors equal 2.
This gives an alternative characterization useful for complexity analysis.
-/

/-- Every prime factor of a power of 2 equals 2. -/
theorem prime_factor_of_pow_two {p m : ℕ} (hp : Nat.Prime p) (h : p ∣ 2 ^ m) :
    p = 2 :=
  le_antisymm (Nat.le_of_dvd (by omega) (hp.dvd_of_dvd_pow h)) hp.two_le

/-- A positive number is a power of 2 iff all its prime factors are 2. -/
theorem pow_two_iff_all_prime_factors_two {d : ℕ} (hd : 0 < d) :
    (∃ k : ℕ, d = 2 ^ k) ↔ ∀ p : ℕ, Nat.Prime p → p ∣ d → p = 2 := by
  constructor
  · rintro ⟨k, rfl⟩ p hp hpd
    exact prime_factor_of_pow_two hp hpd
  · intro hall
    induction d using Nat.strongRecOn with
    | _ d ih =>
      by_cases hd1 : d = 1
      · exact ⟨0, by rw [hd1]⟩
      · have hd2 : 1 < d := by omega
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
        have hp2 : p = 2 := hall p hp hpd
        subst hp2
        obtain ⟨d', rfl⟩ := hpd
        have hd'_pos : 0 < d' := by omega
        have hd'_lt : d' < 2 * d' := by omega
        have hall' : ∀ p : ℕ, Nat.Prime p → p ∣ d' → p = 2 :=
          fun p hp hpd' => hall p hp (dvd_trans hpd' (dvd_mul_left d' 2))
        obtain ⟨k, hk⟩ := ih d' hd'_lt hd'_pos hall'
        exact ⟨k + 1, by rw [hk, pow_succ, mul_comm]⟩

/-
## Part III: Decidability of Constructibility

We show that `IsConstructible α d` is decidable for any α and d.
Since IsConstructible ignores α (it only depends on d), the decision
procedure is purely arithmetic.
-/

/-- Whether d is a power of 2 is decidable, via bounded search.
    If d = 2^k then k < 2^k = d, so we only check k in {0, ..., d}. -/
instance decidable_is_pow_two (d : ℕ) : Decidable (∃ k : ℕ, d = 2 ^ k) := by
  by_cases hd : d = 0
  · exact isFalse (by rintro ⟨k, hk⟩; simp [hd] at hk)
  · exact decidable_of_iff (∃ k ∈ Finset.range (d + 1), d = 2 ^ k) ⟨
      fun ⟨k, _, hk⟩ => ⟨k, hk⟩,
      fun ⟨k, hk⟩ => ⟨k, Finset.mem_range.mpr (by subst hk; exact Nat.lt_succ_of_lt Nat.lt_two_pow_self), hk⟩
    ⟩

/-- Whether d divides some power of 2 is decidable. -/
instance decidable_dvd_some_pow_two (d : ℕ) : Decidable (∃ n : ℕ, d ∣ 2 ^ n) := by
  by_cases hd : d = 0
  · exact isFalse (by subst hd; exact zero_not_dvd_pow_two)
  · exact decidable_of_iff (∃ k : ℕ, d = 2 ^ k)
      (dvd_pow_two_iff_pow_two (by omega)).symm

/-- **Constructibility is decidable**: Given the degree d of the minimal polynomial,
    we can decide whether a number is constructible.
    Since IsConstructible ignores the real number α and depends only on d,
    the decision is purely about whether d > 0 and d is a power of 2. -/
instance decidable_isConstructible (α : ℝ) (d : ℕ) :
    Decidable (IsConstructible α d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-
## Part IV: Decidability of N-gon Constructibility

Via the Gauss-Wantzel theorem, regular n-gon constructibility reduces to
checking whether Euler's totient φ(n) is a power of 2.
-/

/-- Whether φ(n) is a power of 2 is decidable. -/
instance decidable_totientIsPow2 (n : ℕ) : Decidable (TotientIsPow2 n) := by
  unfold TotientIsPow2
  exact decidable_is_pow_two n.totient

/-- N-gon constructibility is decidable for n ≥ 3 via Gauss-Wantzel.
    The decision procedure:
    1. Compute φ(n) (polynomial time via factorization)
    2. Check if φ(n) is a power of 2 (O(log n) divisions) -/
theorem decidable_ngon_constructibility (n : ℕ) (hn : 3 ≤ n) :
    Decidable (IsConstructibleNgon n) :=
  decidable_of_iff (TotientIsPow2 n) (gauss_wantzel_theorem n hn).symm

/-
## Part V: Constructibility Decision Examples

We verify the decidability instance works on concrete examples.
-/

/-- 1 is a valid degree for constructibility (1 = 2^0). -/
example : IsConstructible 0 1 := ⟨by omega, 0, by norm_num⟩

/-- 2 is a valid degree for constructibility (2 = 2^1). -/
example : IsConstructible 0 2 := ⟨by omega, 1, by norm_num⟩

/-- 4 is a valid degree for constructibility (4 = 2^2). -/
example : IsConstructible 0 4 := ⟨by omega, 2, by norm_num⟩

/-- 3 is NOT a valid degree for constructibility. -/
example : ¬IsConstructible 0 3 := by
  intro ⟨_, n, h⟩
  exact AngleTrisection.three_not_dvd_power_of_two n h

/-- 6 is NOT a valid degree for constructibility (6 = 2 × 3). -/
example : ¬IsConstructible 0 6 := by
  intro ⟨_, n, h6⟩
  have h3 : (3 : ℕ) ∣ 6 := by norm_num
  exact AngleTrisection.three_not_dvd_power_of_two n (dvd_trans h3 h6)

/-
## Part VI: Summary and Complexity Analysis

**Input**: A natural number d (the degree of the minimal polynomial over ℚ).
**Question**: Is there a number with this degree that could be constructible?

**Decision procedure**:
1. If d = 0: NO (degree must be positive)
2. Check if d is a power of 2:
   - Repeatedly divide d by 2 until odd
   - If result is 1: YES (d was a power of 2)
   - If result > 1: NO (d has an odd prime factor)

**Complexity**: O(log d) divisions and comparisons.

**For n-gon constructibility** (Gauss-Wantzel):
- Compute φ(n): O(√n) via trial division
- Check if φ(n) is a power of 2: O(log n)
- Total: polynomial in n

The problem of determining constructibility is in P.
-/

/-- The full constructibility characterization: IsConstructible α d ↔ d is a positive power of 2.
    This completely reduces the geometric question to a single arithmetic check. -/
theorem constructibility_iff_pos_pow_two (α : ℝ) (d : ℕ) :
    IsConstructible α d ↔ d > 0 ∧ ∃ k : ℕ, d = 2 ^ k := by
  unfold IsConstructible
  constructor
  · rintro ⟨hd, n, h⟩
    exact ⟨hd, dvd_pow_two_is_pow_two hd h⟩
  · rintro ⟨hd, k, rfl⟩
    exact ⟨by positivity, k, dvd_refl _⟩

/-- Corollary: constructibility is independent of α (depends only on d). -/
theorem constructibility_independent_of_alpha (α β : ℝ) (d : ℕ) :
    IsConstructible α d ↔ IsConstructible β d := by
  simp only [constructibility_iff_pos_pow_two]

end AngleTrisectionOQ03
