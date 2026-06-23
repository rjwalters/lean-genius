import Mathlib
import Proofs.SumOfKthPowersOQ05

/-
# Nat-Congruence Power-Sum Dichotomy mod p (Sum of k-th Powers, OQ-05-OQ-01)

The parent entry `SumOfKthPowersOQ05` proves the modular dichotomy for the complete
power sum over a finite field, specialised to `ZMod p`:

  `∑_{x : ZMod p} x^k = -1`  if `k ≠ 0` and `(p-1) ∣ k`,   and `0` otherwise.

That statement lives in the ring `ZMod p`.  The natural number-theoretic reading is a
congruence between honest natural numbers,

  `∑_{i < p} i^k ≡ (if k ≠ 0 ∧ (p-1) ∣ k then p-1 else 0)  (mod p)`,

where the sum is the ordinary sum of `k`-th powers of the residues `0, 1, …, p-1` taken in
`ℕ`.  This file performs that cast.  The only mathematical content beyond the parent is the
bookkeeping translation between the field-valued sum and the `ℕ`-valued sum:

  * `Nat.cast` is a ring hom, so `(↑(∑ i<p, i^k) : ZMod p) = ∑ i<p, (↑i)^k`;
  * the map `i ↦ (i : ZMod p)` restricted to `range p` is a bijection onto `ZMod p`
    (`Finset.sum_nbij'` with inverse `ZMod.val`), so `∑ i<p, (↑i)^k = ∑ x:ZMod p, x^k`;
  * `(↑(p-1) : ZMod p) = -1` (via `Nat.cast_pred` and `ZMod.natCast_self`), matching the
    `-1` on the field side to the `p-1` on the `ℕ` side.

Concrete instances (e.g. `∑_{i<5} i^4 ≡ 4`, `∑_{i<7} i^6 ≡ 6`) are checked by kernel
`decide`, so they incur no `Lean.ofReduceBool` dependency.  All results are `0`-axiom.
-/

namespace SumOfKthPowersOQ05OQ01

open Finset
open scoped BigOperators

/-- The residue cast `i ↦ (i : ZMod p)` restricted to `range p` is a bijection onto the
whole of `ZMod p` (its inverse is `ZMod.val`); hence the `ℕ`-indexed sum of `k`-th powers
over `range p` agrees with the field-indexed sum over `ZMod p`. -/
theorem sum_range_cast_pow (p : ℕ) [NeZero p] (k : ℕ) :
    (∑ i ∈ Finset.range p, (i : ZMod p) ^ k) = ∑ x : ZMod p, x ^ k :=
  Finset.sum_nbij' (fun i => (i : ZMod p)) (fun x => x.val)
    (fun _ _ => Finset.mem_univ _)
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x))
    (fun _a ha => ZMod.val_natCast_of_lt (Finset.mem_range.mp ha))
    (fun x _ => ZMod.natCast_zmod_val x)
    (fun _ _ => rfl)

/-- **Power-sum dichotomy as a natural-number congruence.**  For a prime `p`, the sum of
`k`-th powers of the residues `0, 1, …, p-1` satisfies

  `∑_{i < p} i^k ≡ (if k ≠ 0 ∧ (p-1) ∣ k then p-1 else 0)  (mod p)`.

This is the `ℕ`-valued face of `SumOfKthPowersOQ05.sum_pow_zmod`. -/
theorem sum_pow_modEq (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (∑ i ∈ Finset.range p, i ^ k) ≡
      (if k ≠ 0 ∧ (p - 1) ∣ k then p - 1 else 0) [MOD p] := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
  simp only [Nat.cast_pow]
  rw [sum_range_cast_pow p k, SumOfKthPowersOQ05.sum_pow_zmod p k]
  by_cases hcond : k ≠ 0 ∧ (p - 1) ∣ k
  · rw [if_pos hcond, if_pos hcond, Nat.cast_pred (Fact.out : p.Prime).pos,
      ZMod.natCast_self]
    ring
  · rw [if_neg hcond, if_neg hcond, Nat.cast_zero]

/-- When `k ≠ 0` and `(p-1) ∣ k`, the power sum is congruent to `p-1 ≡ -1`. -/
theorem sum_pow_modEq_pred (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : k ≠ 0)
    (hdvd : (p - 1) ∣ k) :
    (∑ i ∈ Finset.range p, i ^ k) ≡ p - 1 [MOD p] := by
  have h := sum_pow_modEq p k
  rwa [if_pos ⟨hk, hdvd⟩] at h

/-- Otherwise (either `k = 0`, or `(p-1) ∤ k`), the power sum is divisible by `p`. -/
theorem sum_pow_modEq_zero (p : ℕ) [Fact p.Prime] {k : ℕ}
    (hcond : ¬(k ≠ 0 ∧ (p - 1) ∣ k)) :
    (∑ i ∈ Finset.range p, i ^ k) ≡ 0 [MOD p] := by
  have h := sum_pow_modEq p k
  rwa [if_neg hcond] at h

/-- The power sum is divisible by `p` exactly when we are *not* in the `(p-1) ∣ k`
nonzero-exponent regime. -/
theorem p_dvd_sum_pow_iff (p : ℕ) [Fact p.Prime] (k : ℕ) :
    p ∣ (∑ i ∈ Finset.range p, i ^ k) ↔ ¬(k ≠ 0 ∧ (p - 1) ∣ k) := by
  constructor
  · intro hp
    by_contra hcond
    obtain ⟨hk, hdvd⟩ := hcond
    have h := sum_pow_modEq_pred p hk hdvd
    -- `∑ ≡ 0` and `∑ ≡ p-1` would force `p ∣ p-1`, impossible for a prime.
    have h0 : (∑ i ∈ Finset.range p, i ^ k) ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hp
    have : (0 : ℕ) ≡ p - 1 [MOD p] := h0.symm.trans h
    have hpd : p ∣ (p - 1) := (Nat.modEq_zero_iff_dvd).mp this.symm
    have hlt : p - 1 < p := Nat.sub_lt (Fact.out : p.Prime).pos one_pos
    have hpos : 0 < p - 1 := by
      have := (Fact.out : p.Prime).two_le; omega
    exact absurd (Nat.le_of_dvd hpos hpd) (by omega)
  · intro hcond
    exact (Nat.modEq_zero_iff_dvd).mp (sum_pow_modEq_zero p hcond)

/-- **Sum of residues.** For an odd prime `p`, the residues `0, 1, …, p-1` sum to a
multiple of `p` (the `k = 1` case: `(p-1) ∤ 1` once `p > 2`). -/
theorem sum_residues_modEq (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    (∑ i ∈ Finset.range p, i) ≡ 0 [MOD p] := by
  have h := sum_pow_modEq_zero (p := p) (k := 1) ?_
  · simpa using h
  · rintro ⟨-, hdvd⟩
    have : p - 1 ≤ 1 := Nat.le_of_dvd one_pos hdvd
    omega

/-! ### Concrete instances (verified by kernel `decide`, hence `0`-axiom) -/

/-- `∑_{i<5} i^4 = 354 ≡ 4 (mod 5)`, since `(5-1) ∣ 4`. -/
example : (∑ i ∈ Finset.range 5, i ^ 4) ≡ 4 [MOD 5] := by decide

/-- `∑_{i<5} i^2 = 30 ≡ 0 (mod 5)`, since `(5-1) ∤ 2`. -/
example : (∑ i ∈ Finset.range 5, i ^ 2) ≡ 0 [MOD 5] := by decide

/-- `∑_{i<7} i^6 = 67171 ≡ 6 (mod 7)`, since `(7-1) ∣ 6`. -/
example : (∑ i ∈ Finset.range 7, i ^ 6) ≡ 6 [MOD 7] := by decide

/-- Sum of residues of `ZMod 5` lifted to `ℕ`: `0+1+2+3+4 = 10 ≡ 0 (mod 5)`. -/
example : (∑ i ∈ Finset.range 5, i) ≡ 0 [MOD 5] := by decide

end SumOfKthPowersOQ05OQ01
