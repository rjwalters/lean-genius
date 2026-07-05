/-
The Even Leg of a Primitive Pythagorean Triple is Divisible by 4

Source: Open question (oq-07-oq-01) refining the parity dichotomy of
        pythagorean-triples-oq-07.
Status: VERIFIED (0 axioms, 0 sorries)

The parent result (PythagoreanTriplesOQ07) shows that in a primitive Pythagorean
triple exactly one leg is even. This file strengthens that: the even leg is not
merely even, it is divisible by 4.

The arithmetic heart is a mod-8 refinement of the parent's mod-4 fact:

  * An ODD integer squared is `1 mod 8` (not just `1 mod 4`).
    Reason: (2k+1)² = 4k(k+1) + 1, and k(k+1) is even, so 4k(k+1) ≡ 0 mod 8.

In a primitive triple with even leg `x` (so `y`, `z` odd), the Pythagorean
relation gives `x² = z² − y² ≡ 1 − 1 = 0 (mod 8)`. An even number whose square
is `0 mod 8` must itself be `0 mod 4`: writing `x = 2k`, `x² = 4k² ≡ 0 mod 8`
forces `k` even, i.e. `4 ∣ x`.

Equivalently, in the Euclid parametrisation `x = 2mn` (even leg), `y = m²−n²`,
`z = m²+n²` with `m, n` of opposite parity, `mn` is even, so `4 ∣ 2mn`. The
proof below is parametrisation-free and works directly from the triple relation.
-/

import Mathlib

namespace PythagoreanTriplesEvenLegDivFour

open PythagoreanTriple

variable {x y z : ℤ}

/-! ## Part I: The mod-8 obstruction

The sharper arithmetic fact behind divisibility by 4: an odd integer squared is
`1 mod 8`. This upgrades the parent file's `sq_emod_four_of_odd`. -/

/-- An odd integer squared is `1 mod 8`. -/
theorem sq_emod_eight_of_odd {a : ℤ} (ha : a % 2 = 1) : a * a % 8 = 1 := by
  obtain ⟨k, rfl⟩ := Int.odd_iff.mpr ha
  -- k(k+1) is even: two consecutive integers, one is even.
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
  have h : (2 * k + 1) * (2 * k + 1) = 4 * (k * (k + 1)) + 1 := by ring
  omega

/-! ## Part II: An even square that is `0 mod 8` gives a factor of 4

If `x` is even and `x² ≡ 0 (mod 8)`, then `4 ∣ x`. -/

/-- If an even integer's square is `0 mod 8`, the integer is divisible by `4`. -/
theorem four_dvd_of_even_sq_emod_eight {a : ℤ} (ha : a % 2 = 0)
    (h8 : a * a % 8 = 0) : 4 ∣ a := by
  obtain ⟨k, rfl⟩ := Int.even_iff.mpr ha
  -- (k+k)² = 4k², and 4k² ≡ 0 mod 8 forces k even.
  have hsq : (k + k) * (k + k) = 4 * (k * k) := by ring
  have hkk : k * k % 2 = 0 := by omega
  -- k*k even ⇒ k even
  have hke : Even k := by
    have he2 : Even (k * k) := Int.even_iff.mpr hkk
    rcases Int.even_mul.mp he2 with hk | hk <;> exact hk
  obtain ⟨j, rfl⟩ := hke
  -- a = (j+j)+(j+j) = 4j
  exact ⟨j, by ring⟩

/-! ## Part III: In a primitive triple the even leg's square is `0 mod 8`

If `x` is the even leg (so, by coprimality, `y` is odd and hence `z` is odd),
then `x² = z² − y² ≡ 1 − 1 = 0 (mod 8)`. -/

/-- In a primitive triple with even leg `x`, the odd companion leg `y` and the
hypotenuse `z` are both odd, so `x² ≡ 0 (mod 8)`. -/
theorem even_leg_sq_emod_eight (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1)
    (hx : x % 2 = 0) : x * x % 8 = 0 := by
  have he : x * x + y * y = z * z := h
  -- Coprimality forces the other leg odd.
  have hy : y % 2 = 1 := by
    rcases h.even_odd_of_coprime hc with ⟨_, hy1⟩ | ⟨hx1, _⟩
    · exact hy1
    · omega
  -- The hypotenuse is odd: z² = x² + y² ≡ 0 + 1 = 1 mod 4, so z is odd.
  have hz : z % 2 = 1 := by
    have hx4 : x * x % 4 = 0 := by
      obtain ⟨k, rfl⟩ := Int.even_iff.mpr hx
      have : (k + k) * (k + k) = 4 * (k * k) := by ring
      omega
    have hy4 : y * y % 4 = 1 := by
      obtain ⟨k, rfl⟩ := Int.odd_iff.mpr hy
      have : (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 := by ring
      omega
    rcases Int.emod_two_eq_zero_or_one z with hz0 | hz1
    · exfalso
      obtain ⟨k, rfl⟩ := Int.even_iff.mpr hz0
      have : (k + k) * (k + k) = 4 * (k * k) := by ring
      omega
    · exact hz1
  -- odd squares are 1 mod 8; combine.
  have hyy := sq_emod_eight_of_odd hy
  have hzz := sq_emod_eight_of_odd hz
  omega

/-! ## Part IV: The even leg is divisible by 4 -/

/-- If `x` is the even leg of a primitive triple, then `4 ∣ x`. -/
theorem four_dvd_of_even_leg (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1)
    (hx : x % 2 = 0) : 4 ∣ x :=
  four_dvd_of_even_sq_emod_eight hx (even_leg_sq_emod_eight h hc hx)

/-- **Main theorem.** In a primitive Pythagorean triple, exactly one leg is even
and that leg is divisible by `4`: either `4 ∣ x` (with `y` odd), or `4 ∣ y`
(with `x` odd). -/
theorem four_dvd_even_leg (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1) :
    (4 ∣ x ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ 4 ∣ y) := by
  rcases h.even_odd_of_coprime hc with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl ⟨four_dvd_of_even_leg h hc hx, hy⟩
  · -- swap to the symmetric triple y x z to reuse the even-leg lemma
    have h' : PythagoreanTriple y x z := by
      have he : x * x + y * y = z * z := h
      show y * y + x * x = z * z
      linarith
    have hc' : Int.gcd y x = 1 := by rwa [Int.gcd_comm] at hc
    exact Or.inr ⟨hx, four_dvd_of_even_leg h' hc' hy⟩

/-- **Even/Odd packaging.** The even leg of a primitive triple is a multiple of
`4`. -/
theorem four_dvd_even_leg' (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1) :
    (4 ∣ x ∧ Odd y) ∨ (Odd x ∧ 4 ∣ y) := by
  rcases four_dvd_even_leg h hc with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl ⟨hx, Int.odd_iff.mpr hy⟩
  · exact Or.inr ⟨Int.odd_iff.mpr hx, hy⟩

end PythagoreanTriplesEvenLegDivFour
