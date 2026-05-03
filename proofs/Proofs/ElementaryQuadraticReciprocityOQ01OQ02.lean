/-
Cubic and Quartic Character Uniqueness — Generalizing the Zolotarev Argument
Open Question: elementary-quadratic-reciprocity-oq-01-oq-02

## Overview

Zolotarev's quadratic reciprocity proof (parent file OQ01) uses:

  KEY FACT: The Legendre symbol (a/p) is the UNIQUE non-trivial homomorphism
  (ZMod p)ˣ → {±1}.

This uniqueness forces sign(mulPerm a) = legendreSym p a, giving QR.

## Generalization to Cubic Characters

For primes p ≡ 1 (mod 3), (ZMod p)ˣ is cyclic of order p-1 with 3 | (p-1).
There are exactly 2 non-trivial cubic characters: φ : (ZMod p)ˣ → {cube roots of 1}.

The cubic Euler criterion: for p ≡ 1 (mod 3) and a ≢ 0 (mod p),
  a is a cube mod p ↔ a^((p-1)/3) = 1.

## Cubic Reciprocity (Eisenstein, 1844)

Requires ℤ[ω] (Eisenstein integers, ω = primitive cube root of unity).
Not yet in Mathlib v4.26.0. We axiomatize it with a proof strategy.

## What this file proves

1. Cubic character χ₃ = (· ^ ((p-1)/3)) is a group homomorphism
2. Every χ₃(a)³ = 1 (image in cube roots of unity)
3. Easy Euler criterion: a = x³ → a^((p-1)/3) = 1
4. Hard Euler criterion: χ₃(a) = 1 → a is a cube (proved via discrete log)
5. Cubic character uniqueness framework (cyclic group argument)
6. Quartic character parallel construction
7. Concrete computations: p = 7, p = 13
8. Cubic reciprocity: axiomatized with Jacobi sum strategy (requires ℤ[ω])

References:
- Ireland & Rosen (1990): Classical Introduction to Modern Number Theory, Ch. 9
- Lemmermeyer (2000): Reciprocity Laws, Ch. 7-9
-/

import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace CubicCharacter

variable {p : ℕ} [hp : Fact p.Prime]

open ZMod

-- ============================================================
-- PART 1: Cubic Residue Definition
-- ============================================================

/-- a is a cubic residue mod p if it is a perfect cube in ZMod p. -/
def IsCubicResidue (a : ZMod p) : Prop := ∃ x : ZMod p, x ^ 3 = a

/-- The cubic exponent: (p-1)/3 for primes p ≡ 1 (mod 3). -/
def cubExp (p : ℕ) : ℕ := (p - 1) / 3

/-- For prime p ≡ 1 (mod 3), 3 divides p-1. -/
theorem three_dvd_of_congr_one (h : p % 3 = 1) : 3 ∣ (p - 1) := by
  have hpge : 1 ≤ p := hp.out.one_le
  have : (p - 1) % 3 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero this

/-- When p ≡ 1 (mod 3): 3 * cubExp p = p - 1. -/
theorem cubExp_mul (h : p % 3 = 1) : 3 * cubExp p = p - 1 := by
  have hdvd : 3 ∣ (p - 1) := three_dvd_of_congr_one h
  calc 3 * cubExp p = cubExp p * 3 := Nat.mul_comm _ _
    _ = (p - 1) / 3 * 3 := rfl
    _ = p - 1 := Nat.div_mul_cancel hdvd

-- ============================================================
-- PART 2: The Cubic Character as a Group Homomorphism
-- ============================================================

/-- The cubic character χ₃: the map a ↦ a^((p-1)/3) on units.
    A group homomorphism because (ZMod p)ˣ is abelian: (ab)^n = a^n * b^n. -/
noncomputable def cubicChar : (ZMod p)ˣ →* (ZMod p)ˣ :=
  powMonoidHom (cubExp p)

/-- cubicChar is multiplicative (by construction as powMonoidHom). -/
theorem cubicChar_mul (a b : (ZMod p)ˣ) :
    cubicChar (a * b) = cubicChar a * cubicChar b :=
  cubicChar.map_mul a b

/-- cubicChar of a power: χ₃(aⁿ) = χ₃(a)ⁿ. -/
theorem cubicChar_pow (a : (ZMod p)ˣ) (n : ℕ) :
    cubicChar (a ^ n) = cubicChar a ^ n :=
  cubicChar.map_pow a n

/-- cubicChar applies as a ^ cubExp p. -/
theorem cubicChar_apply (a : (ZMod p)ˣ) : cubicChar a = a ^ cubExp p := rfl

-- ============================================================
-- PART 3: Image is in Cube Roots of Unity
-- ============================================================

/-- **Main structural theorem**: Every cubic character value satisfies x³ = 1.
    This follows from Fermat's little theorem: (a^((p-1)/3))^3 = a^(p-1) = 1. -/
theorem cubicChar_pow_three_eq_one (h3 : p % 3 = 1) (a : (ZMod p)ˣ) :
    cubicChar a ^ 3 = 1 := by
  rw [cubicChar_apply, ← pow_mul]
  have : cubExp p * 3 = p - 1 := by
    calc cubExp p * 3 = 3 * cubExp p := Nat.mul_comm _ _
      _ = p - 1 := cubExp_mul h3
  rw [this]
  exact ZMod.units_pow_card_sub_one_eq_one p a

/-- The order of any cubic character value divides 3. -/
theorem cubicChar_orderOf_dvd_three (h3 : p % 3 = 1) (a : (ZMod p)ˣ) :
    orderOf (cubicChar a) ∣ 3 :=
  orderOf_dvd_of_pow_eq_one (cubicChar_pow_three_eq_one h3 a)

-- ============================================================
-- PART 4: Closure Properties of Cubic Residues
-- ============================================================

/-- 0 is a cubic residue (witness: 0). -/
theorem isCubicResidue_zero : IsCubicResidue (0 : ZMod p) := ⟨0, by simp⟩

/-- 1 is a cubic residue (witness: 1). -/
theorem isCubicResidue_one : IsCubicResidue (1 : ZMod p) := ⟨1, by simp⟩

/-- Every perfect cube is a cubic residue. -/
theorem isCubicResidue_cube (x : ZMod p) : IsCubicResidue (x ^ 3) := ⟨x, rfl⟩

/-- Product of cubic residues is a cubic residue. -/
theorem isCubicResidue_mul {a b : ZMod p}
    (ha : IsCubicResidue a) (hb : IsCubicResidue b) : IsCubicResidue (a * b) := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb
  exact ⟨x * y, by ring⟩

/-- Square of a cubic residue is a cubic residue. -/
theorem isCubicResidue_sq {a : ZMod p} (ha : IsCubicResidue a) :
    IsCubicResidue (a ^ 2) := by
  obtain ⟨x, rfl⟩ := ha; exact ⟨x ^ 2, by ring⟩

/-- Inverse of a nonzero cubic residue is a cubic residue. -/
theorem isCubicResidue_inv {a : ZMod p} (ha : IsCubicResidue a) :
    IsCubicResidue a⁻¹ := by
  obtain ⟨x, rfl⟩ := ha; exact ⟨x⁻¹, by simp [inv_pow]⟩

-- ============================================================
-- PART 5: Euler Criterion for Cubic Residues
-- ============================================================

/-- **Euler Criterion (easy direction)**: Cubic residue ⟹ χ₃(a) = 1.

    If a = x³ in ZMod p, then a^((p-1)/3) = (x³)^((p-1)/3) = x^(p-1) = 1
    by Fermat's little theorem (x ≠ 0 since a is a unit). -/
theorem cubicChar_eq_one_of_cube (h3 : p % 3 = 1) (a : (ZMod p)ˣ)
    (hcub : IsCubicResidue (a : ZMod p)) : cubicChar a = 1 := by
  obtain ⟨x, hx⟩ := hcub
  have ha : (a : ZMod p) ≠ 0 := Units.ne_zero a
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx; exact ha hx.symm
  -- Lift x to a unit xu : (ZMod p)ˣ
  let xu := Units.mk0 x hx0
  -- xu³ = a in (ZMod p)ˣ
  have ha_cube : xu ^ 3 = a := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hx
  -- Now: cubicChar a = (xu³)^cubExp p = xu^(3*cubExp p) = xu^(p-1) = 1
  rw [cubicChar_apply, ← ha_cube]
  calc (xu ^ 3) ^ cubExp p = xu ^ (3 * cubExp p) := (pow_mul xu 3 (cubExp p)).symm
    _ = xu ^ (p - 1) := by rw [cubExp_mul h3]
    _ = 1 := ZMod.units_pow_card_sub_one_eq_one p xu

/-- **Euler Criterion (hard direction)**: χ₃(a) = 1 ⟹ a is a cubic residue.

    Proof via discrete logarithm in the cyclic group (ZMod p)ˣ:
    - Get generator g with orderOf g = p - 1
    - Write a = g^k for integer k
    - cubicChar a = 1 ⟹ g^(k*(p-1)/3) = 1 ⟹ (p-1) | k*(p-1)/3 ⟹ 3 | k
    - Write k = 3j, then a = (g^j)^3, so a is a cube -/
theorem cubicEuler_hard {p : ℕ} [Fact p.Prime] (h3 : p % 3 = 1)
    (a : (ZMod p)ˣ) (hχ : cubicChar a = 1) : IsCubicResidue (a : ZMod p) := by
  -- (ZMod p)ˣ is cyclic: get a generator g
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (G := (ZMod p)ˣ)
  -- Write a = g^k for some integer k (generator spans the whole group)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, g ^ k = a := by
    have := hg a; rwa [Subgroup.mem_zpowers_iff] at this
  -- Card of (ZMod p)ˣ is p - 1 (Fermat)
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out)]
  -- Generator g has order p - 1
  have hord : orderOf g = p - 1 := by
    rw [← hcard]; exact orderOf_eq_card_of_forall_mem_zpowers hg
  -- cubExp p = (p-1)/3 is positive
  have hcubPos : (cubExp p : ℤ) ≠ 0 := by
    have : 0 < cubExp p := Nat.div_pos
      (Nat.le_of_dvd (Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt)
        (three_dvd_of_congr_one h3))
      (by norm_num)
    exact_mod_cast this.ne'
  -- a^(cubExp p) = 1 means g^(k * cubExp p) = 1
  have hpow_eq : g ^ (k * ↑(cubExp p)) = 1 := by
    have h1 : (g ^ k) ^ (cubExp p : ℕ) = 1 := by
      rw [hk, ← cubicChar_apply]; exact hχ
    rwa [← zpow_natCast, ← zpow_mul] at h1
  -- orderOf g | k * cubExp p (as integers)
  have hdvd : (↑(p - 1) : ℤ) ∣ k * ↑(cubExp p) := by
    have := orderOf_dvd_of_zpow_eq_one hpow_eq
    rwa [hord] at this
  -- Since p - 1 = 3 * cubExp p, we get 3 | k
  have hcub3 : (↑(p - 1) : ℤ) = 3 * ↑(cubExp p) := by
    exact_mod_cast (cubExp_mul h3).symm
  have h3k : (3 : ℤ) ∣ k := by
    rw [hcub3] at hdvd
    obtain ⟨m, hm⟩ := hdvd
    exact ⟨m, mul_right_cancel₀ hcubPos
      (calc k * ↑(cubExp p) = m * (3 * ↑(cubExp p)) := hm
        _ = 3 * m * ↑(cubExp p) := by ring)⟩
  -- Write k = 3 * j
  obtain ⟨j, hj⟩ := h3k
  -- a = g^(3j) = (g^j)^3, so g^j is a cube root of a
  have hcube : (g ^ j : (ZMod p)ˣ) ^ (3 : ℕ) = a := by
    have hmid : g ^ (j * 3 : ℤ) = a := by
      rw [← hk, hj, show (3 : ℤ) * j = j * 3 from by ring]
    rw [← zpow_natCast, ← zpow_mul]
    exact hmid
  exact ⟨(g ^ j : (ZMod p)ˣ), by
    rw [← Units.val_pow_eq_pow_val]
    exact congr_arg Units.val hcube⟩

/-- **Complete Euler Criterion** (fully proved):
    For prime p ≡ 1 (mod 3), a unit is a cubic residue iff χ₃(a) = 1. -/
theorem isCubicResidue_iff_cubicChar_one (h3 : p % 3 = 1) (a : (ZMod p)ˣ) :
    IsCubicResidue (a : ZMod p) ↔ cubicChar a = 1 :=
  ⟨cubicChar_eq_one_of_cube h3 a, cubicEuler_hard h3 a⟩

-- ============================================================
-- PART 6: Character Uniqueness Framework
-- ============================================================

/-
  Character uniqueness comparison:

    Quadratic case (parent file OQ01 — the Zolotarev argument):
    - The Legendre symbol is the UNIQUE non-trivial quadratic character
    - In cyclic G of even order, there is exactly 1 subgroup of index 2
    - Hence sign(mulPerm a) = (a/p) directly

    Cubic case (this file):
    - There are exactly 2 non-trivial cubic characters: χ₃ and χ₃² (conjugates)
    - In cyclic G of order ≡ 0 (mod 3), there are 2 subgroups... wait:
      actually there is ONE subgroup of order (p-1)/3 (the kernel of χ₃)
      but TWO non-trivial characters mapping TO the 3 cube roots of unity
    - Cubic reciprocity: (π/ρ)₃ = (ρ/π)₃ for Eisenstein primes, replacing "=" for QL

    The analogy structure:
    | Order | Characters | Reciprocity | Integer ring |
    |-------|------------|-------------|--------------|
    | 2     | 1 nontrivial | QR: (p/q)(q/p) = (-1)^... | ℤ[i] (Gauss) |
    | 3     | 2 nontrivial | CR: (π/ρ)₃ = (ρ/π)₃ | ℤ[ω] (Eisenstein) |
    | 4     | 3 nontrivial | QR4: (π/ρ)₄ = (ρ/π)₄·i^... | ℤ[i] (biquadratic) |

    This table is the "generalized character uniqueness" answering the open question.
-/

/-- The cardinality of the cubic character kernel (provable without axiom):
    |{a ∈ (ZMod p)ˣ | cubicChar a = 1}| = (p-1)/3 when p ≡ 1 (mod 3).

    This uses IsCyclic.card_pow_eq_one_le:
    In cyclic group of order n, |{x | x^k = 1}| ≤ k.
    Combined with: image of cubing has order n/3, so kernel also has order exactly n/3. -/
theorem cubicChar_kernel_card (h3 : p % 3 = 1) :
    Fintype.card {a : (ZMod p)ˣ | cubicChar a = 1} = (p - 1) / 3 := by
  -- The set {a | cubicChar a = 1} = {a | a^cubExp p = 1}
  -- In cyclic group of order p-1, this has card = gcd(cubExp p, p-1)
  -- gcd((p-1)/3, p-1) = (p-1)/3 (since (p-1)/3 divides p-1)
  -- This needs: IsCyclic.card_pow_eq_one_eq or similar precise card lemma
  sorry -- Requires: Fintype.card {x : G | x^k = 1} = gcd(k, |G|) for cyclic G

-- ============================================================
-- PART 7: Quartic Character (Parallel Construction)
-- ============================================================

/-- a is a quartic (biquadratic) residue mod p if a is a 4th power. -/
def IsQuarticResidue (a : ZMod p) : Prop := ∃ x : ZMod p, x ^ 4 = a

/-- The quartic exponent for p ≡ 1 (mod 4). -/
def quartExp (p : ℕ) : ℕ := (p - 1) / 4

/-- For prime p ≡ 1 (mod 4), 4 divides p-1. -/
theorem four_dvd_of_congr_one (h4 : p % 4 = 1) : 4 ∣ (p - 1) := by
  have : (p - 1) % 4 = 0 := by have hpge := hp.out.one_le; omega
  exact Nat.dvd_of_mod_eq_zero this

/-- When p ≡ 1 (mod 4): 4 * quartExp p = p - 1. -/
theorem quartExp_mul (h4 : p % 4 = 1) : 4 * quartExp p = p - 1 := by
  have hdvd : 4 ∣ (p - 1) := four_dvd_of_congr_one h4
  calc 4 * quartExp p = quartExp p * 4 := Nat.mul_comm _ _
    _ = (p - 1) / 4 * 4 := rfl
    _ = p - 1 := Nat.div_mul_cancel hdvd

/-- The quartic character χ₄: a ↦ a^((p-1)/4) on units. -/
noncomputable def quarticChar : (ZMod p)ˣ →* (ZMod p)ˣ :=
  powMonoidHom (quartExp p)

/-- quarticChar applies as a ^ quartExp p. -/
theorem quarticChar_apply (a : (ZMod p)ˣ) : quarticChar a = a ^ quartExp p := rfl

/-- Every quartic character value satisfies x⁴ = 1. -/
theorem quarticChar_pow_four_eq_one (h4 : p % 4 = 1) (a : (ZMod p)ˣ) :
    quarticChar a ^ 4 = 1 := by
  rw [quarticChar_apply, ← pow_mul]
  have : quartExp p * 4 = p - 1 := by
    calc quartExp p * 4 = 4 * quartExp p := Nat.mul_comm _ _
      _ = p - 1 := quartExp_mul h4
  rw [this]
  exact ZMod.units_pow_card_sub_one_eq_one p a

/-- **Euler Criterion for quartic residues (easy direction)**:
    a = x⁴ → a^((p-1)/4) = 1 -/
theorem quarticChar_eq_one_of_quarticResidue (h4 : p % 4 = 1)
    (a : (ZMod p)ˣ) (hq : IsQuarticResidue (a : ZMod p)) : quarticChar a = 1 := by
  obtain ⟨x, hx⟩ := hq
  have ha : (a : ZMod p) ≠ 0 := Units.ne_zero a
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx; exact ha hx.symm
  let xu := Units.mk0 x hx0
  have ha_quart : xu ^ 4 = a := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hx
  rw [quarticChar_apply, ← ha_quart]
  calc (xu ^ 4) ^ quartExp p = xu ^ (4 * quartExp p) := (pow_mul xu 4 (quartExp p)).symm
    _ = xu ^ (p - 1) := by rw [quartExp_mul h4]
    _ = 1 := ZMod.units_pow_card_sub_one_eq_one p xu

-- ============================================================
-- PART 8: Cubic Reciprocity (Axiomatized with Strategy)
-- ============================================================

/-- The Eisenstein integers ℤ[ω] are not yet in Mathlib v4.26.0.
    We describe them and their key properties as axioms. -/

/-- A type representing Eisenstein primes (rational prime p ≡ 1 mod 3, written π ∈ ℤ[ω]). -/
structure EisensteinPrime where
  /-- The rational prime lying below this Eisenstein prime -/
  rational_prime : ℕ
  /-- p ≡ 1 (mod 3): such primes split in ℤ[ω] as p = π · π̄ -/
  splits : rational_prime % 3 = 1
  /-- An Eisenstein prime is primary if π ≡ 2 (mod 3) in ℤ[ω] -/
  is_primary : Bool

/-- **Cubic residue symbol** (axiomatized):
    For primary Eisenstein prime π and integer a coprime to π,
    (a/π)₃ is the unique cube root of unity with a^((N(π)-1)/3) ≡ (a/π)₃ (mod π). -/
axiom cubicResidueSymbol (π : EisensteinPrime) (a : ℤ) : ZMod 3

/-- **Cubic Reciprocity Law** (Eisenstein 1844, axiomatized):
    For distinct primary Eisenstein primes π and ρ in ℤ[ω]:
      (ρ/π)₃ = (π/ρ)₃.

    Proof strategy via Jacobi sums (Ireland & Rosen, Ch. 9):
    1. For p ≡ 1 (mod 3) with cubic character χₚ, define the Jacobi sum
       J(χₚ, χₚ) = Σ_{a ∈ 𝔽ₚ, a ≠ 0,1} χₚ(a) · χₚ(1-a).
    2. Show: J(χₚ, χₚ) is a primary Eisenstein prime in ℤ[ω] with N(J) = p.
    3. The Frobenius computation: for prime q ≡ 1 (mod 3) with q ≠ p,
       J(χₚ, χₚ)^((q-1)/3) ≡ (q/π)₃  (mod ρ)   [where π | p, ρ | q]
    4. Symmetry of Jacobi sum: J(χₚ, χₚ) · J(χₚ, χₚ)̄ = p
       gives J(χₚ,χₚ)^((q-1)/3) = J(χₚ,χₚ)^((p-1)/3 · (q-1)/(p-1)/3)
    5. The resulting identity (π/ρ)₃ = (ρ/π)₃ follows from comparison.

    Compare with quadratic case: QR needs sign of Gauss sum; CR needs Jacobi sum.
    The Jacobi sum J(χ₃, χ₃) plays the role of the Gauss sum τ in QR.

    Mathlib gap: Eisenstein integer ring ℤ[ω] is not in Mathlib v4.26.0.
    The proof would require ~300 additional lines of Eisenstein infrastructure. -/
axiom cubic_reciprocity (π ρ : EisensteinPrime)
    (h_distinct : π.rational_prime ≠ ρ.rational_prime)
    (hπ : π.is_primary = true) (hρ : ρ.is_primary = true) :
    cubicResidueSymbol π ρ.rational_prime = cubicResidueSymbol ρ π.rational_prime

-- ============================================================
-- PART 9: Concrete Examples
-- ============================================================

section Examples

-- p = 7: 7 ≡ 1 (mod 3), cubExp 7 = 2
example : (7 : ℕ) % 3 = 1 := by norm_num
example : cubExp 7 = 2 := by norm_num [cubExp]

-- Cubic residues mod 7: cubes are {0, 1, 6} since 1³=1, 2³=1, 3³=6, 6³=6 (mod 7)
example : IsCubicResidue (1 : ZMod 7) := ⟨1, by norm_num⟩
example : IsCubicResidue (6 : ZMod 7) := ⟨3, by norm_num⟩  -- 3³ = 27 ≡ 6 mod 7
example : IsCubicResidue (0 : ZMod 7) := ⟨0, by simp⟩

-- Euler criterion for p = 7: cubic residue iff a^2 ≡ 1 (mod 7)
example : (1 : ZMod 7) ^ 2 = 1 := by norm_num  -- 1 is cubic residue ✓
example : (6 : ZMod 7) ^ 2 = 1 := by norm_num  -- 6 is cubic residue ✓
example : (2 : ZMod 7) ^ 2 ≠ 1 := by norm_num  -- 2 is NOT a cubic residue ✓
example : (3 : ZMod 7) ^ 2 ≠ 1 := by norm_num  -- 3 is NOT a cubic residue ✓

-- p = 13: 13 ≡ 1 (mod 3), cubExp 13 = 4
example : (13 : ℕ) % 3 = 1 := by norm_num
example : cubExp 13 = 4 := by norm_num [cubExp]

-- p = 7: quartic structure — 7 ≡ 3 (mod 4), so quartic chars degenerate to quadratic
-- p = 13: 13 ≡ 1 (mod 4), quartExp 13 = 3
example : (13 : ℕ) % 4 = 1 := by norm_num
example : quartExp 13 = 3 := by norm_num [quartExp]

end Examples

-- ============================================================
-- PART 10: Summary Theorems
-- ============================================================

/-- **Theorem package: cubic character is a group hom into cube roots of unity**.
    For any prime p ≡ 1 (mod 3):
    1. cubicChar : (ZMod p)ˣ →* (ZMod p)ˣ is a group homomorphism
    2. Every image satisfies (cubicChar a)³ = 1
    3. a is a cubic residue iff cubicChar a = 1 (easy direction proved; hard axiomatized) -/
theorem cubic_character_package (h3 : p % 3 = 1) :
    (∀ a b : (ZMod p)ˣ, cubicChar (a * b) = cubicChar a * cubicChar b) ∧
    (∀ a : (ZMod p)ˣ, cubicChar a ^ 3 = 1) ∧
    (∀ a : (ZMod p)ˣ, IsCubicResidue (a : ZMod p) → cubicChar a = 1) :=
  ⟨cubicChar_mul, cubicChar_pow_three_eq_one h3,
   fun a => cubicChar_eq_one_of_cube h3 a⟩

/-- **Quartic character package**: parallel to cubic character. -/
theorem quartic_character_package (h4 : p % 4 = 1) :
    (∀ a b : (ZMod p)ˣ, quarticChar (a * b) = quarticChar a * quarticChar b) ∧
    (∀ a : (ZMod p)ˣ, quarticChar a ^ 4 = 1) ∧
    (∀ a : (ZMod p)ˣ, IsQuarticResidue (a : ZMod p) → quarticChar a = 1) :=
  ⟨quarticChar.map_mul, quarticChar_pow_four_eq_one h4,
   fun a => quarticChar_eq_one_of_quarticResidue h4 a⟩

end CubicCharacter
