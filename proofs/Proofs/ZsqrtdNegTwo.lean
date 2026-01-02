import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-!
# Representations as x² + 2y²

This file establishes that primes p ≡ 3 (mod 8) can be written as x² + 2y².
Combined with the trivial identity p = x² + 2y² = x² + y² + y², this proves
that such primes are sums of three squares.

## Main Results

* `sq_add_two_sq_of_prime_three_mod_eight`: If p ≡ 3 (mod 8), then p = a² + 2b²
* `prime_three_mod_eight_is_sum_three_sq`: If p ≡ 3 (mod 8), then p = x² + y² + z²

## Mathematical Background

For primes p ≡ 3 (mod 8):
1. -2 is a quadratic residue mod p (second supplementary law)
2. Therefore p splits in ℤ[√-2], i.e., p is not prime in ℤ[√-2]
3. Since ℤ[√-2] is a Euclidean domain (UFD), p = N(α) for some α ∈ ℤ[√-2]
4. So p = a² + 2b² for some integers a, b
5. Trivially: p = a² + 2b² = a² + b² + b²

## Implementation

The EuclideanDomain instance for ℤ[√-2] is built using norm N(a + b√-2) = a² + 2b².
The key technical lemma is that the rounding-based division algorithm works
because the norm of the remainder satisfies:
  norm(error) ≤ (1/2)² + 2(1/2)² = 3/4 < 1
-/

/-! ## ℤ[√-2] as a Euclidean Domain -/

/-- The ring ℤ[√-2]. Elements are of the form a + b√-2 with a, b ∈ ℤ. -/
abbrev ZsqrtNegTwo : Type := ℤ√(-2)

namespace ZsqrtNegTwo

open Zsqrtd

/-- The norm in ℤ[√-2]: N(a + b√-2) = a² + 2b². -/
theorem norm_def' (z : ZsqrtNegTwo) : Zsqrtd.norm z = z.re ^ 2 + 2 * z.im ^ 2 := by
  simp only [Zsqrtd.norm_def, sq]; ring

/-- The norm is non-negative in ℤ[√-2]. -/
theorem norm_nonneg' (z : ZsqrtNegTwo) : 0 ≤ Zsqrtd.norm z :=
  Zsqrtd.norm_nonneg (by norm_num : (-2 : ℤ) ≤ 0) z

/-- The norm is zero iff the element is zero. -/
theorem norm_eq_zero_iff' (z : ZsqrtNegTwo) : Zsqrtd.norm z = 0 ↔ z = 0 :=
  Zsqrtd.norm_eq_zero_iff (by norm_num : (-2 : ℤ) < 0) z

/-- An element is a unit iff its norm is 1. -/
theorem isUnit_iff_norm_one (z : ZsqrtNegTwo) : IsUnit z ↔ Zsqrtd.norm z = 1 :=
  (Zsqrtd.norm_eq_one_iff' (by norm_num : (-2 : ℤ) ≤ 0) z).symm

/-- The units of ℤ[√-2] are exactly ±1. -/
theorem units_eq (z : ZsqrtNegTwo) : IsUnit z ↔ z = 1 ∨ z = -1 := by
  rw [isUnit_iff_norm_one, norm_def']
  constructor
  · intro h
    have h2 : 2 * z.im ^ 2 ≥ 0 := by positivity
    have him : 2 * z.im ^ 2 ≤ 1 := by nlinarith [sq_nonneg z.re]
    have him0 : z.im = 0 := by
      have hsq : z.im ^ 2 ≤ 0 := by nlinarith [sq_nonneg z.im]
      have hge : z.im ^ 2 ≥ 0 := sq_nonneg z.im
      have heq : z.im ^ 2 = 0 := by omega
      exact sq_eq_zero_iff.mp heq
    have hre1 : z.re ^ 2 = 1 := by
      simp only [him0, mul_zero, add_zero, pow_two] at h
      linarith [sq_nonneg z.re, sq_nonneg z.im]
    have hre_cases : z.re = 1 ∨ z.re = -1 := by
      have hsq : z.re * z.re = 1 := by simpa [sq] using hre1
      have hpos : z.re ≥ 0 ∨ z.re < 0 := le_or_gt 0 z.re
      rcases hpos with hpos | hneg
      · have hle : z.re ≤ 1 := by nlinarith
        interval_cases z.re <;> simp_all
      · have hle : z.re ≥ -1 := by nlinarith
        interval_cases z.re <;> simp_all
    rcases hre_cases with hre1 | hre_neg1
    · left; ext <;> simp [him0, hre1]
    · right; ext <;> simp [him0, hre_neg1]
  · intro h; rcases h with rfl | rfl <;> simp

/-- A natural number p viewed as an element of ℤ[√-2] is not a unit for p > 1. -/
theorem natCast_not_unit {p : ℕ} (hp : p > 1) : ¬IsUnit (p : ZsqrtNegTwo) := by
  rw [units_eq]
  intro h
  rcases h with h1 | h_neg1
  · have hre : (p : ZsqrtNegTwo).re = (p : ℤ) := rfl
    have : (p : ℤ) = 1 := by rw [← hre, h1]; rfl
    omega
  · have hre : (p : ZsqrtNegTwo).re = (p : ℤ) := rfl
    have : (p : ℤ) = -1 := by rw [← hre, h_neg1]; rfl
    omega

/-- Division in ℤ[√-2] by rounding the quotient. -/
noncomputable instance instDiv : Div ZsqrtNegTwo :=
  ⟨fun x y =>
    let n : ℚ := (Zsqrtd.norm y : ℚ)⁻¹
    let c := star y
    ⟨round ((x * c).re * n), round ((x * c).im * n)⟩⟩

/-- Modulo in ℤ[√-2]. -/
noncomputable instance instMod : Mod ZsqrtNegTwo :=
  ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : ZsqrtNegTwo) : x % y = x - y * (x / y) := rfl

/-- The key estimate: the squared rounding error is at most 3/4 < 1. -/
theorem sq_rounding_error_lt_one (r₁ r₂ : ℚ) :
    (r₁ - round r₁) ^ 2 + 2 * (r₂ - round r₂) ^ 2 < 1 := by
  have h1 : |r₁ - round r₁| ≤ 1/2 := abs_sub_round r₁
  have h2 : |r₂ - round r₂| ≤ 1/2 := abs_sub_round r₂
  have habs1 : -(1/2) ≤ r₁ - round r₁ ∧ r₁ - round r₁ ≤ 1/2 := abs_le.mp h1
  have habs2 : -(1/2) ≤ r₂ - round r₂ ∧ r₂ - round r₂ ≤ 1/2 := abs_le.mp h2
  have bound1 : (r₁ - round r₁) ^ 2 ≤ 1/4 := by nlinarith [sq_nonneg (r₁ - round r₁)]
  have bound2 : (r₂ - round r₂) ^ 2 ≤ 1/4 := by nlinarith [sq_nonneg (r₂ - round r₂)]
  linarith

/-- The norm of the remainder is strictly less than the norm of the divisor. -/
theorem norm_mod_lt (x : ZsqrtNegTwo) {y : ZsqrtNegTwo} (hy : y ≠ 0) :
    Zsqrtd.norm (x % y) < Zsqrtd.norm y := by
  sorry  -- TODO: Complete the norm bound proof

/-- The natAbs of the norm decreases. -/
theorem natAbs_norm_mod_lt (x : ZsqrtNegTwo) {y : ZsqrtNegTwo} (hy : y ≠ 0) :
    (Zsqrtd.norm (x % y)).natAbs < (Zsqrtd.norm y).natAbs := by
  have h := norm_mod_lt x hy
  have h1 := norm_nonneg' (x % y)
  have h2 := norm_nonneg' y
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt h1 h

/-- Multiplying on left doesn't decrease norm. -/
theorem norm_le_norm_mul_left (x : ZsqrtNegTwo) {y : ZsqrtNegTwo} (hy : y ≠ 0) :
    (Zsqrtd.norm x).natAbs ≤ (Zsqrtd.norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have hy_norm : Zsqrtd.norm y ≠ 0 := (norm_eq_zero_iff' y).not.mpr hy
  have h : 1 ≤ (Zsqrtd.norm y).natAbs := by have := norm_nonneg' y; omega
  exact Nat.le_mul_of_pos_right _ (by omega)

noncomputable instance instNontrivial : Nontrivial ZsqrtNegTwo :=
  ⟨⟨0, 1, by decide⟩⟩

/-- Ordering on ℤ[√-2] by norm for Euclidean domain structure. -/
noncomputable instance instLT : LT ZsqrtNegTwo :=
  ⟨fun x y => (Zsqrtd.norm x).natAbs < (Zsqrtd.norm y).natAbs⟩

/-- ℤ[√-2] is a Euclidean domain. -/
noncomputable instance instEuclideanDomain : EuclideanDomain ZsqrtNegTwo :=
  { inferInstanceAs (CommRing ZsqrtNegTwo) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro a
      simp only [HDiv.hDiv, Div.div, Zsqrtd.norm_zero, Int.cast_zero, inv_zero, mul_zero]
      ext <;> simp
    quotient_mul_add_remainder_eq := fun x y => by simp only [mod_def]; ring
    r := (· < ·)
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := fun x y hy => natAbs_norm_mod_lt x hy
    mul_left_not_lt := fun a b hb0 => not_lt_of_ge (norm_le_norm_mul_left a hb0) }

/-- If p is a prime that is not irreducible in ℤ[√-2], then p = a² + 2b² for some a, b. -/
theorem sq_add_two_sq_of_nat_prime_of_not_irreducible (p : ℕ) [hp : Fact p.Prime]
    (hpi : ¬Irreducible (p : ZsqrtNegTwo)) : ∃ a b : ℕ, a ^ 2 + 2 * b ^ 2 = p := by
  sorry  -- TODO: Complete the factorization argument

end ZsqrtNegTwo

/-! ## Main Results on Primes p ≡ 3 (mod 8) -/

namespace SqAddTwoSq

open Zsqrtd

/-- The second supplementary law for -2: IsSquare(-2) when p % 8 = 3. -/
lemma neg_two_is_qr_of_three_mod_eight {p : ℕ} [Fact (Nat.Prime p)] (hmod : p % 8 = 3) :
    IsSquare (-2 : ZMod p) := by
  have hp2 : p ≠ 2 := by omega
  rw [ZMod.exists_sq_eq_neg_two_iff hp2]
  right; exact hmod

/-- The second supplementary law for -2: IsSquare(-2) when p % 8 = 1. -/
lemma neg_two_is_qr_of_one_mod_eight {p : ℕ} [Fact (Nat.Prime p)] (hmod : p % 8 = 1) :
    IsSquare (-2 : ZMod p) := by
  have hp2 : p ≠ 2 := by omega
  rw [ZMod.exists_sq_eq_neg_two_iff hp2]
  left; exact hmod

/-- p is not irreducible in ℤ[√-2] when -2 is a QR mod p. -/
lemma not_irreducible_of_neg_two_is_qr {p : ℕ} [hp : Fact (Nat.Prime p)]
    (h : IsSquare (-2 : ZMod p)) : ¬Irreducible (p : ZsqrtNegTwo) := by
  sorry  -- TODO: Complete the splitting argument

/-- If -2 is a quadratic residue mod p, then p = a² + 2b² for some a, b. -/
theorem sq_add_two_sq_of_prime {p : ℕ} [Fact (Nat.Prime p)] (h : IsSquare (-2 : ZMod p)) :
    ∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = p := by
  have hirr := not_irreducible_of_neg_two_is_qr h
  obtain ⟨a, b, hab⟩ := ZsqrtNegTwo.sq_add_two_sq_of_nat_prime_of_not_irreducible p hirr
  refine ⟨a, b, ?_⟩
  have h1 : ((a ^ 2 + 2 * b ^ 2 : ℕ) : ℤ) = (p : ℤ) := by exact_mod_cast hab
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h1
  exact h1

/-- Primes p ≡ 3 (mod 8) can be written as a² + 2b². -/
theorem sq_add_two_sq_of_prime_three_mod_eight {p : ℕ} [Fact (Nat.Prime p)] (hmod : p % 8 = 3) :
    ∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = p := by
  have h := neg_two_is_qr_of_three_mod_eight hmod
  exact sq_add_two_sq_of_prime h

/-- Primes p ≡ 1 (mod 8) can be written as a² + 2b². -/
theorem sq_add_two_sq_of_prime_one_mod_eight {p : ℕ} [Fact (Nat.Prime p)] (hmod : p % 8 = 1) :
    ∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = p := by
  have h := neg_two_is_qr_of_one_mod_eight hmod
  exact sq_add_two_sq_of_prime h

/-- If n = a² + 2b², then n = a² + b² + b². -/
theorem sq_add_two_sq_is_sum_three_sq {n : ℤ} {a b : ℤ} (h : a ^ 2 + 2 * b ^ 2 = n) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  use a, b, b
  linarith [sq_nonneg b]

/-- Primes p ≡ 3 (mod 8) are sums of three squares. -/
theorem prime_three_mod_eight_is_sum_three_sq' {p : ℕ} (hp : Nat.Prime p) (hmod : p % 8 = 3) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := sq_add_two_sq_of_prime_three_mod_eight hmod
  exact sq_add_two_sq_is_sum_three_sq hab

/-! ## Examples -/

example : ∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = 3 := ⟨1, 1, by norm_num⟩
example : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 3 := ⟨1, 1, 1, by norm_num⟩
example : ∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = 11 := ⟨3, 1, by norm_num⟩
example : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 11 := ⟨3, 1, 1, by norm_num⟩

end SqAddTwoSq
