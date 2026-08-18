import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Nonvanishing of the prime-frequency scalar

For `d ≥ 4` and a complex root of unity, the scalar
`d - 1 - (ζ + ζ⁻¹)` cannot vanish: the left summand has norm at least
three, while the sum of a unit-modulus number and its inverse has norm at
most two.
-/

namespace Erdos85

theorem complex_frequencyScalar_ne_zero
    {d p : ℕ} [NeZero p] (hd : 4 ≤ d) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ p) :
    (d : ℂ) - 1 - (ζ + ζ⁻¹) ≠ 0 := by
  intro hzero
  have heq : (d : ℂ) - 1 = ζ + ζ⁻¹ := sub_eq_zero.mp hzero
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one (NeZero.ne p)
  have hupper : ‖ζ + ζ⁻¹‖ ≤ 2 := by
    calc
      ‖ζ + ζ⁻¹‖ ≤ ‖ζ‖ + ‖ζ⁻¹‖ := norm_add_le _ _
      _ = 2 := by rw [hnorm, norm_inv, hnorm]; norm_num
  rw [← heq] at hupper
  have hcast : (d : ℂ) - 1 = ((d - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  rw [hcast, Complex.norm_natCast] at hupper
  have hnat : d - 1 ≤ 2 := by exact_mod_cast hupper
  omega

end Erdos85
