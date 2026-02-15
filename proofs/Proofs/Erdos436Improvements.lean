/-
Erdős Problem #436: Improvements and Axiom Elimination

This file proves two axioms from Erdos436Problem.lean using Mathlib's
Legendre symbol and Euler criterion machinery:

1. euler_criterion_backward: The backward direction of Euler's criterion
   (a^((p-1)/2) ≡ 1 mod p → a is a QR)
2. qr_product_non_residues: Product of two quadratic non-residues is a QR
   (via Legendre symbol multiplicativity)

These proofs bridge between the ℕ-based definitions in Erdos436Problem
and ZMod-based Mathlib APIs.
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

open ZMod Nat Classical

namespace Erdos436Improvements

-- Reproduce definitions from Erdos436Problem for self-containment
def IsKthPowerResidue (r k p : ℕ) : Prop :=
  ∃ x : ℕ, x ^ k % p = r % p

def IsQuadraticResidue (r p : ℕ) : Prop := IsKthPowerResidue r 2 p

/-
## Bridge Lemmas: ZMod ↔ ℕ
-/

/-- Bridge: IsSquare in ZMod p gives a natural number witness for our definition. -/
theorem isSquare_to_kth_residue (a p : ℕ) (hp : Nat.Prime p)
    (hsq : IsSquare (a : ZMod p)) : IsKthPowerResidue a 2 p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := hsq
  refine ⟨r.val, ?_⟩
  have := congr_arg ZMod.val hr
  rw [ZMod.val_natCast] at this
  rw [ZMod.val_mul] at this
  rw [sq]
  exact this.symm

/-- Bridge: not a kth power residue in ℕ implies not IsSquare in ZMod. -/
theorem not_kth_residue_to_not_isSquare (a p : ℕ) (hp : Nat.Prime p)
    (h : ¬IsKthPowerResidue a 2 p) : ¬IsSquare (a : ZMod p) :=
  fun hsq => h (isSquare_to_kth_residue a p hp hsq)

/-- Helper: a % p ≠ 0 implies (a : ZMod p) ≠ 0. -/
theorem nat_mod_ne_to_zmod_ne (a p : ℕ) (hp : Nat.Prime p)
    (ha : a % p ≠ 0) : (a : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h; apply ha
  rwa [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at h

/-- For prime p > 2, p - 1 is even. -/
theorem prime_sub_one_even (p : ℕ) (hp : Nat.Prime p) (hp_gt2 : p > 2) :
    2 ∣ (p - 1) := by
  have hodd := hp.odd_of_ne_two (by omega)
  rw [Nat.odd_iff] at hodd
  omega

/-
## Theorem 1: Euler's Criterion (backward direction)

Previously axiomatized in Erdos436Problem.lean.
Now proved using Mathlib's `ZMod.euler_criterion`.
-/

/-- Euler's criterion (backward): if a^((p-1)/2) ≡ 1 (mod p) then a is a QR.
    Uses Mathlib's ZMod.euler_criterion and bridge lemmas. -/
theorem euler_criterion_backward (a p : ℕ) (hp : Nat.Prime p) (hp_odd : p > 2)
    (ha : a % p ≠ 0) (hpow : a ^ ((p - 1) / 2) % p = 1) :
    IsQuadraticResidue a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha_zmod := nat_mod_ne_to_zmod_ne a p hp ha
  -- (p-1)/2 = p/2 for odd prime p
  have hp_div : (p - 1) / 2 = p / 2 := by
    have hodd := hp.odd_of_ne_two (by omega)
    rw [Nat.odd_iff] at hodd; omega
  -- Lift the ℕ modular equation to ZMod equality
  have hpow_zmod : (a : ZMod p) ^ (p / 2) = 1 := by
    rw [← hp_div]
    have h1 : ((a ^ ((p - 1) / 2) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff']
      rw [hpow, Nat.mod_eq_of_lt hp.one_lt]
    simp only [Nat.cast_pow, Nat.cast_one] at h1
    exact h1
  -- Apply Mathlib's Euler criterion, then bridge back to ℕ
  exact isSquare_to_kth_residue a p hp ((ZMod.euler_criterion p ha_zmod).mpr hpow_zmod)

/-
## Theorem 2: Product of Non-Residues

Previously axiomatized in Erdos436Problem.lean.
Now proved using Legendre symbol multiplicativity.
-/

/-- Product of two quadratic non-residues is a quadratic residue (for odd prime p).
    Uses Legendre symbol: (a/p) = (b/p) = -1 implies (ab/p) = (-1)(-1) = 1. -/
theorem qr_product_non_residues (a b p : ℕ) (hp : Nat.Prime p) (hp_odd : p % 2 = 1)
    (ha : ¬IsKthPowerResidue a 2 p) (hb : ¬IsKthPowerResidue b 2 p)
    (ha_nz : a % p ≠ 0) (hb_nz : b % p ≠ 0) :
    IsKthPowerResidue (a * b) 2 p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha_zmod := nat_mod_ne_to_zmod_ne a p hp ha_nz
  have hb_zmod := nat_mod_ne_to_zmod_ne b p hp hb_nz
  have ha_nsq := not_kth_residue_to_not_isSquare a p hp ha
  have hb_nsq := not_kth_residue_to_not_isSquare b p hp hb
  -- Work entirely with ℤ-casted values for legendreSym compatibility
  -- The key lemma: legendreSym.eq_neg_one_iff operates on ℤ → ZMod casts
  -- We need to show our ℕ → ZMod facts match the ℤ → ZMod versions
  -- Convert ℕ → ZMod facts to ℤ → ZMod for legendreSym API
  -- The cast (↑(a : ℤ) : ZMod p) equals (↑(a : ℕ) : ZMod p) via Int.cast_natCast
  have cast_eq_a : ((a : ℤ) : ZMod p) = ((a : ℕ) : ZMod p) := Int.cast_natCast a
  have cast_eq_b : ((b : ℤ) : ZMod p) = ((b : ℕ) : ZMod p) := Int.cast_natCast b
  have ha_neg : legendreSym p (a : ℤ) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    rw [show ((a : ℤ) : ZMod p) = ((a : ℕ) : ZMod p) from cast_eq_a]
    exact ha_nsq
  have hb_neg : legendreSym p (b : ℤ) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    rw [show ((b : ℤ) : ZMod p) = ((b : ℕ) : ZMod p) from cast_eq_b]
    exact hb_nsq
  -- Product: (-1) * (-1) = 1
  have hab_leg : legendreSym p ((a : ℤ) * (b : ℤ)) = 1 := by
    rw [legendreSym.mul, ha_neg, hb_neg]; ring
  -- Convert to IsSquare via eq_one_iff
  have hab_nz : (((a : ℤ) * (b : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
    exact mul_ne_zero ha_zmod hb_zmod
  have hab_sq : IsSquare (((a : ℤ) * (b : ℤ) : ℤ) : ZMod p) :=
    (legendreSym.eq_one_iff p hab_nz).mp hab_leg
  -- Bridge: the ℤ product cast = ℕ product cast in ZMod
  have hab_sq' : IsSquare ((a * b : ℕ) : ZMod p) := by
    have : ((a * b : ℕ) : ZMod p) = (((a : ℤ) * (b : ℤ) : ℤ) : ZMod p) := by
      rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Nat.cast_mul]
    rw [this]; exact hab_sq
  exact isSquare_to_kth_residue (a * b) p hp hab_sq'

/-
## Summary

Two axioms from Erdos436Problem.lean have been eliminated:
1. `euler_criterion_backward` → proved via ZMod.euler_criterion
2. `qr_product_non_residues` → proved via legendreSym multiplicativity

Key technique: Bridge lemmas that convert between:
- ℕ-based `IsKthPowerResidue r k p` (∃ x, x^k % p = r % p)
- ZMod-based `IsSquare (a : ZMod p)` (∃ r, a = r * r)

This reduces the axiom count of the formalization by 2.
-/

end Erdos436Improvements
