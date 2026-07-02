/-
# Hermite's Sawtooth Companion Identity  (hermite-floor-identity, OQ-03 #1)

The parent `HermiteFloorIdentity.lean` proves Hermite's floor identity
  ∑_{k=0}^{n-1} ⌊x + k/n⌋ = ⌊n·x⌋.
Its first open question asks for the **companion fractional-part (sawtooth)
identity**
  ∑_{k=0}^{n-1} {x + k/n} = {n·x} + (n-1)/2,
where `{y} = Int.fract y = y - ⌊y⌋` is the sawtooth function.

This file proves exactly that.  The derivation is a one-line consequence of the
parent identity together with the Gauss sum `∑_{k<n} k = n(n-1)/2`:
  ∑ {x+k/n} = ∑ (x + k/n) − ∑ ⌊x+k/n⌋
            = (n·x + (n-1)/2) − ⌊n·x⌋       (Hermite for the floor sum)
            = (n·x − ⌊n·x⌋) + (n-1)/2
            = {n·x} + (n-1)/2.

We also record two clean specialisations:

* `hermite_fract_sum_at_zero` : ∑_{k<n} {k/n} = (n-1)/2   (the classical fact
  that the fractional parts `0, 1/n, …, (n-1)/n` average to `(n-1)/(2n)`);
* `hermite_fract_sum_of_mul_int` : if `n·x ∈ ℤ` (so `{n·x} = 0`) then the sawtooth
  sum is exactly `(n-1)/2`.

## Main results
- `hermite_fract_identity`        : ∑_{k<n} {x+k/n} = {n·x} + (n-1)/2   (n ≥ 1)
- `hermite_fract_sum_at_zero`     : ∑_{k<n} {k/n}   = (n-1)/2
- `hermite_fract_sum_of_mul_int`  : n·x ∈ ℤ ⇒ ∑_{k<n} {x+k/n} = (n-1)/2
-/
import Mathlib
import Proofs.HermiteFloorIdentity

open Finset

namespace HermiteFloorIdentityOQ03

/-- Gauss sum, real-valued: `∑_{k<m} k = m(m-1)/2` for every `m`. -/
lemma sum_range_cast (m : ℕ) :
    ∑ k ∈ Finset.range m, (k : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **Hermite's sawtooth (fractional-part) companion identity.**  For every real
    `x` and every `n ≥ 1`,
      `∑_{k=0}^{n-1} {x + k/n} = {n·x} + (n-1)/2`,
    the additive twin of the floor identity `∑ ⌊x + k/n⌋ = ⌊n·x⌋`. -/
theorem hermite_fract_identity (x : ℝ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range n, Int.fract (x + (k : ℝ) / (n : ℝ))
      = Int.fract ((n : ℝ) * x) + ((n : ℝ) - 1) / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [Int.fract]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.sum_div, sum_range_cast n, ← Int.cast_sum,
      HermiteFloorIdentity.hermite_floor_identity x n hn]
  field_simp
  ring

/-- **Specialisation at `x = 0`.**  The fractional parts `0, 1/n, 2/n, …, (n-1)/n`
    sum to `(n-1)/2`: `∑_{k=0}^{n-1} {k/n} = (n-1)/2`. -/
theorem hermite_fract_sum_at_zero (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range n, Int.fract ((k : ℝ) / (n : ℝ)) = ((n : ℝ) - 1) / 2 := by
  have h := hermite_fract_identity 0 n hn
  simp only [zero_add, mul_zero, Int.fract_zero] at h
  exact h

/-- **Specialisation when `n·x` is an integer.**  If `{n·x} = 0` (equivalently
    `n·x ∈ ℤ`), the sawtooth sum is exactly `(n-1)/2`. -/
theorem hermite_fract_sum_of_mul_int (x : ℝ) (n : ℕ) (hn : 0 < n)
    (hx : Int.fract ((n : ℝ) * x) = 0) :
    ∑ k ∈ Finset.range n, Int.fract (x + (k : ℝ) / (n : ℝ)) = ((n : ℝ) - 1) / 2 := by
  rw [hermite_fract_identity x n hn, hx, zero_add]

end HermiteFloorIdentityOQ03
