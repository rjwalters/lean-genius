import Mathlib
import Proofs.SumOfKthPowersOQ05

/-
# Power Sums mod `p`: the Natural-Number Congruence (Sum of k-th Powers, OQ-05-OQ-01)

The parent entry (`SumOfKthPowersOQ05`) proves the complete power sum over a finite
field, and its `ZMod p` specialisation

  `∑_{x : ZMod p} x^k = -1`  if `k ≠ 0` and `(p-1) ∣ k`,   and `0` otherwise.

That statement lives in the *ring* `ZMod p`.  The elementary number-theoretic face of the
same fact — the form actually used to prove divisibilities like `p ∣ ∑_{i<p} i^k` — is a
congruence between honest natural numbers:

  `∑_{i=0}^{p-1} i^k ≡ (if k ≠ 0 and (p-1) ∣ k then p-1 else 0)  (mod p).`

This entry carries the `ZMod p` dichotomy down to `ℕ`.  The bridge is a reindexing of the
sum over the whole field by the residues `0, 1, …, p-1` (a bijection `range p ≃ ZMod p`
via `Nat.cast` / `ZMod.val`), followed by the `Nat.cast`/`ModEq` correspondence
`(↑a = ↑b in ZMod p) ↔ a ≡ b [MOD p]`.  The `-1` of the field becomes the residue `p-1`.

Consequences:
* `p ∣ ∑_{i<p} i^k` holds **exactly** when it is *not* the case that `k ≠ 0` and `(p-1)∣k`
  (the divisibility criterion behind the standard "vanishing of low power sums").
* the residues `0,1,…,p-1` sum to a multiple of `p` for every odd prime (`k = 1`).
* an integer version `∑_{i<p} (i:ℤ)^k ≡ -1 (mod p)` recovering the field's `-1` directly.

All results are `0`-axiom; the concrete examples use kernel `decide` (not the
compiler-trusting `native_decide`), so no `Lean.ofReduceBool` dependency is incurred.
-/

namespace SumOfKthPowersOQ05OQ01

open Finset
open scoped BigOperators

/-- **Reindexing bridge.** The cast to `ZMod p` of the natural-number power sum over
`range p` equals the complete power sum over `ZMod p`.  The residues `0, 1, …, p-1`
biject with `ZMod p` via `Nat.cast` (inverse `ZMod.val`). -/
theorem sum_range_pow_cast (p : ℕ) [NeZero p] (k : ℕ) :
    ((∑ i ∈ Finset.range p, i ^ k : ℕ) : ZMod p) = ∑ x : ZMod p, x ^ k := by
  push_cast
  symm
  apply Finset.sum_bij' (fun (x : ZMod p) _ => ZMod.val x) (fun (i : ℕ) _ => (i : ZMod p))
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro i _; exact Finset.mem_univ _
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro i hi; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hi)
  · intro x _; rw [ZMod.natCast_zmod_val]

/-- **Power-sum congruence mod `p`.** For a prime `p`,
`∑_{i=0}^{p-1} i^k ≡ (if k ≠ 0 and (p-1) ∣ k then p-1 else 0)  (mod p)`.
This is the natural-number form of the `ZMod p` dichotomy
(`SumOfKthPowersOQ05.sum_pow_zmod`). -/
theorem sum_range_pow_modEq (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (∑ i ∈ Finset.range p, i ^ k)
      ≡ (if k ≠ 0 ∧ (p - 1) ∣ k then p - 1 else 0) [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff, sum_range_pow_cast p k,
    SumOfKthPowersOQ05.sum_pow_zmod p k]
  split_ifs with h
  · -- residue `p-1` casts to `-1` in `ZMod p`
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    rw [Nat.cast_sub hp1, ZMod.natCast_self, Nat.cast_one, zero_sub]
  · rw [Nat.cast_zero]

/-- The `-1` face: when `k ≠ 0` and `(p-1) ∣ k`, the power sum is congruent to `p-1`
(equivalently `-1`) mod `p`. -/
theorem sum_range_pow_modEq_neg_one (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : k ≠ 0) (hdvd : (p - 1) ∣ k) :
    (∑ i ∈ Finset.range p, i ^ k) ≡ p - 1 [MOD p] := by
  have h := sum_range_pow_modEq p k
  rwa [if_pos ⟨hk, hdvd⟩] at h

/-- **Divisibility criterion.** `p` divides `∑_{i<p} i^k` precisely when it is *not*
the case that `k ≠ 0` and `(p-1) ∣ k`. -/
theorem dvd_sum_range_pow_iff (p : ℕ) [Fact p.Prime] (k : ℕ) :
    p ∣ (∑ i ∈ Finset.range p, i ^ k) ↔ ¬ (k ≠ 0 ∧ (p - 1) ∣ k) := by
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [← Nat.modEq_zero_iff_dvd]
  constructor
  · intro h hcond
    have hres : (p - 1 : ℕ) ≡ 0 [MOD p] :=
      ((sum_range_pow_modEq_neg_one p k hcond.1 hcond.2).symm).trans h
    have : p ∣ (p - 1) := (Nat.modEq_zero_iff_dvd).mp hres
    have := Nat.le_of_dvd (by omega) this
    omega
  · intro hcond
    have h := sum_range_pow_modEq p k
    rwa [if_neg hcond] at h

/-- **Sum of residues.** For an odd prime `p`, the residues `0, 1, …, p-1`
sum to a multiple of `p` (the `k = 1` case, where `(p-1) ∤ 1` once `p > 2`). -/
theorem sum_range_self_modEq_zero (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    (∑ i ∈ Finset.range p, i) ≡ 0 [MOD p] := by
  have h := sum_range_pow_modEq p 1
  simp only [pow_one] at h
  rw [if_neg] at h
  · exact h
  · rintro ⟨-, hdvd⟩
    have := Nat.le_of_dvd one_pos hdvd
    omega

/-- **Integer form.** When `k ≠ 0` and `(p-1) ∣ k`, the integer power sum over the
residues is congruent to `-1` mod `p`, recovering the `-1` of `FiniteField.sum_pow_units`
directly (without rewriting `-1` as `p-1`). -/
theorem sum_range_pow_intModEq_neg_one (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : k ≠ 0) (hdvd : (p - 1) ∣ k) :
    (∑ i ∈ Finset.range p, (i : ℤ) ^ k) ≡ -1 [ZMOD p] := by
  have hnat := sum_range_pow_modEq_neg_one p k hk hdvd
  have hint : ((∑ i ∈ Finset.range p, i ^ k : ℕ) : ℤ) ≡ ((p - 1 : ℕ) : ℤ) [ZMOD p] :=
    Int.natCast_modEq_iff.mpr hnat
  have hcast : ((∑ i ∈ Finset.range p, i ^ k : ℕ) : ℤ)
      = ∑ i ∈ Finset.range p, (i : ℤ) ^ k := by push_cast; ring
  rw [hcast] at hint
  refine hint.trans ?_
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [Int.modEq_iff_dvd]
  refine ⟨-1, ?_⟩
  have hsub : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp1, Nat.cast_one]
  rw [hsub]; ring

/-! ### Concrete instances (verified by `decide`, hence `0`-axiom) -/

/-- `∑_{i<5} i^4 = 354 ≡ 4 = 5-1 (mod 5)`, since `4 ≠ 0` and `(5-1) ∣ 4`. -/
example : (∑ i ∈ Finset.range 5, i ^ 4) ≡ 4 [MOD 5] := by decide

/-- `∑_{i<5} i^2 = 30 ≡ 0 (mod 5)`, since `(5-1) ∤ 2`. -/
example : (∑ i ∈ Finset.range 5, i ^ 2) ≡ 0 [MOD 5] := by decide

/-- `∑_{i<7} i^6 ≡ 6 = 7-1 (mod 7)`, since `(7-1) ∣ 6`. -/
example : (∑ i ∈ Finset.range 7, i ^ 6) ≡ 6 [MOD 7] := by decide

/-- `5 ∣ ∑_{i<5} i^2` (the divisibility criterion, since `(5-1) ∤ 2`). -/
example : 5 ∣ (∑ i ∈ Finset.range 5, i ^ 2) := by decide

/-- `5 ∤ ∑_{i<5} i^4` (since `(5-1) ∣ 4`, the sum is `≡ -1`). -/
example : ¬ 5 ∣ (∑ i ∈ Finset.range 5, i ^ 4) := by decide

end SumOfKthPowersOQ05OQ01
