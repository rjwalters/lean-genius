import Mathlib
import Proofs.ZsqrtdNegTwoOQ03

/-!
# ℤ[ω] (Eisenstein integers), child OQ-03-OQ-06: the unit group

A child of `zsqrtd-neg-two-oq-03`, which builds the Eisenstein-integer ring
`ℤ[ω]` (with `ω² + ω + 1 = 0`), its multiplicative norm `N(a + bω) = a² - ab + b²`,
and its `EuclideanDomain` structure on the way to representing primes `p ≡ 1 mod 3`
as `a² + 3b²`.

This entry determines the **unit group of `ℤ[ω]` completely**: an element is a unit
iff its norm is `1`, and there are **exactly six** such elements — the sixth roots
of unity `{±1, ±ω, ±ω²}`, in coordinates
`{⟨1,0⟩, ⟨-1,0⟩, ⟨0,1⟩, ⟨0,-1⟩, ⟨1,1⟩, ⟨-1,-1⟩}`.

Results:
* `isUnit_iff_norm_eq_one` — `IsUnit z ↔ N z = 1` (norm is multiplicative and
  norm-1 elements are inverted by their conjugate).
* `norm_eq_one_iff` — the exact list of the six norm-`1` elements, via
  `4·N(z) = (2re - im)² + 3·im²` bounding both coordinates to `{-1,0,1}`.
* `isUnit_iff` — the combined element-level classification of units.
* `unitsFinset`, `card_unitsFinset` (`= 6`), `isUnit_iff_mem_unitsFinset`.

All results are `0`-axiom (no `sorry`, no `axiom`, no `native_decide`).

## References
* The Eisenstein integers `ℤ[ω]` and their six units (sixth roots of unity).
-/

open Proofs Proofs.Eisenstein

namespace ZsqrtdNegTwoOQ03OQ06

/-- `ω`, the primitive cube root of unity generating `ℤ[ω]` (coordinates `⟨0,1⟩`). -/
def omega : Eisenstein := ⟨0, 1⟩

/-!
## Section 1: Units are exactly the norm-1 elements
-/

/-- **A norm-`1` element is a unit**, inverted by its conjugate
    (`z · conj z = ⟨N z, 0⟩ = 1`). Conversely a unit has norm dividing `1`, and
    since the norm of a nonzero element is a positive integer, it equals `1`. -/
theorem isUnit_iff_norm_eq_one (z : Eisenstein) : IsUnit z ↔ norm z = 1 := by
  constructor
  · intro h
    obtain ⟨u, rfl⟩ := h
    have hzw : (↑u : Eisenstein) * ↑u⁻¹ = 1 := u.mul_inv
    have hd : norm (↑u : Eisenstein) ∣ 1 :=
      ⟨norm (↑u⁻¹ : Eisenstein), by rw [← norm_mul, hzw, norm_one]⟩
    have hpos : 0 < norm (↑u : Eisenstein) := norm_pos_of_ne_zero u.ne_zero
    have hle : norm (↑u : Eisenstein) ≤ 1 := Int.le_of_dvd (by norm_num) hd
    omega
  · intro hz
    have h1 : z * conj z = 1 := by rw [mul_conj, hz]; ext <;> simp
    have h2 : conj z * z = 1 := by rw [mul_comm]; exact h1
    exact ⟨⟨z, conj z, h1, h2⟩, rfl⟩

/-!
## Section 2: Enumerating the six units
-/

/-- **Classification of norm-`1` Eisenstein integers.** The norm equals `1` exactly
    for the six sixth-roots of unity `{±1, ±ω, ±ω²}`. From the identity
    `4·N(z) = (2re - im)² + 3·im²`, both coordinates are squeezed into `{-1,0,1}`,
    leaving nine candidates of which exactly six have norm `1`. -/
theorem norm_eq_one_iff (z : Eisenstein) :
    norm z = 1 ↔
      z = ⟨1, 0⟩ ∨ z = ⟨-1, 0⟩ ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ ∨
      z = ⟨1, 1⟩ ∨ z = ⟨-1, -1⟩ := by
  constructor
  · intro hz
    obtain ⟨a, b⟩ := z
    have hz' : a ^ 2 - a * b + b ^ 2 = 1 := hz
    have hid1 : (2 * a - b) ^ 2 + 3 * b ^ 2 = 4 := by linear_combination 4 * hz'
    have hid2 : (2 * b - a) ^ 2 + 3 * a ^ 2 = 4 := by linear_combination 4 * hz'
    have htb : 3 * b ^ 2 ≤ 4 := by nlinarith [hid1, sq_nonneg (2 * a - b)]
    have hta : 3 * a ^ 2 ≤ 4 := by nlinarith [hid2, sq_nonneg (2 * b - a)]
    have hb2 : b ^ 2 ≤ 1 := by
      by_contra h
      push_neg at h
      have : (2 : ℤ) ≤ b ^ 2 := Int.add_one_le_iff.mpr h
      linarith
    have ha2 : a ^ 2 ≤ 1 := by
      by_contra h
      push_neg at h
      have : (2 : ℤ) ≤ a ^ 2 := Int.add_one_le_iff.mpr h
      linarith
    have hblo : -1 ≤ b := by nlinarith [hb2, sq_nonneg (b + 1)]
    have hbhi : b ≤ 1 := by nlinarith [hb2, sq_nonneg (b - 1)]
    have halo : -1 ≤ a := by nlinarith [ha2, sq_nonneg (a + 1)]
    have hahi : a ≤ 1 := by nlinarith [ha2, sq_nonneg (a - 1)]
    interval_cases a <;> interval_cases b <;> revert hz' <;> decide
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

/-- **Element-level classification of the units of `ℤ[ω]`.** `z` is a unit iff it is
    one of the six sixth-roots of unity. -/
theorem isUnit_iff (z : Eisenstein) :
    IsUnit z ↔
      z = ⟨1, 0⟩ ∨ z = ⟨-1, 0⟩ ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ ∨
      z = ⟨1, 1⟩ ∨ z = ⟨-1, -1⟩ :=
  (isUnit_iff_norm_eq_one z).trans (norm_eq_one_iff z)

/-!
## Section 3: The unit group has exactly six elements
-/

/-- The six units of `ℤ[ω]` as a `Finset`: `{±1, ±ω, ±ω²}`. -/
def unitsFinset : Finset Eisenstein :=
  {⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩}

/-- **There are exactly six units.** -/
theorem card_unitsFinset : unitsFinset.card = 6 := by decide

/-- Membership form of the unit classification: the units of `ℤ[ω]` are exactly
    the six elements of `unitsFinset`. -/
theorem isUnit_iff_mem_unitsFinset (z : Eisenstein) :
    IsUnit z ↔ z ∈ unitsFinset := by
  rw [isUnit_iff]
  simp only [unitsFinset, Finset.mem_insert, Finset.mem_singleton]

end ZsqrtdNegTwoOQ03OQ06
