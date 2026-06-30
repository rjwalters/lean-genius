/-
Parity Dichotomy: Exactly One Leg of a Primitive Pythagorean Triple is Even

Source: Open question from pythagorean-triples gallery proof
Status: VERIFIED (0 axioms, 0 sorries)

In a primitive Pythagorean triple x² + y² = z² with coprime legs, exactly one
leg is even and the other odd. There are two ingredients:

  * BOTH ODD is impossible for ANY Pythagorean triple (coprimality not needed):
    an odd square is 1 mod 4, so a sum of two odd squares is 2 mod 4, which is
    never a perfect square (Int.sq_ne_two_mod_four).

  * BOTH EVEN is excluded by coprimality: 2 would divide gcd(x, y) = 1.

Together they give the dichotomy. Mathlib packages the coprime statement as
`PythagoreanTriple.even_odd_of_coprime`; the genuine content surfaced here is
the standalone "both odd is impossible" obstruction, which holds for every
triple and is the arithmetic heart of why no primitive triple has two odd legs.
-/

import Mathlib

namespace PythagoreanTriplesParity

open PythagoreanTriple

variable {x y z : ℤ}

/-! ## Part I: The mod-4 obstruction

The single arithmetic fact behind the whole dichotomy: an odd integer squared
is `1 mod 4`. -/

/-- An odd integer squared is `1 mod 4`. -/
theorem sq_emod_four_of_odd {a : ℤ} (ha : a % 2 = 1) : a * a % 4 = 1 := by
  obtain ⟨k, rfl⟩ := Int.odd_iff.mpr ha
  have h : (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 := by ring
  omega

/-! ## Part II: Both legs odd is impossible (for every triple)

This needs NO coprimality hypothesis. If both legs were odd then
`x² + y² ≡ 2 (mod 4)`, but `x² + y² = z²` and a square is never `2 mod 4`. -/

/-- For ANY Pythagorean triple, the two legs cannot both be odd. -/
theorem not_both_odd (h : PythagoreanTriple x y z) :
    ¬(x % 2 = 1 ∧ y % 2 = 1) := by
  rintro ⟨hx, hy⟩
  have hxx := sq_emod_four_of_odd hx
  have hyy := sq_emod_four_of_odd hy
  have hz := Int.sq_ne_two_mod_four z
  have he : x * x + y * y = z * z := h
  omega

/-! ## Part III: Both legs even is impossible (under coprimality)

If both legs were even, `2 ∣ gcd(x, y) = 1`, a contradiction. We obtain it as a
consequence of Mathlib's `even_odd_of_coprime`. -/

/-- For a primitive triple (coprime legs), the two legs cannot both be even. -/
theorem not_both_even (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1) :
    ¬(x % 2 = 0 ∧ y % 2 = 0) := by
  rintro ⟨hx, hy⟩
  rcases h.even_odd_of_coprime hc with ⟨_, hy1⟩ | ⟨hx1, _⟩ <;> omega

/-! ## Part IV: The parity dichotomy

Combining: exactly one leg is even and the other odd. -/

/-- **Parity dichotomy** (mod-2 form). In a primitive Pythagorean triple,
either `x` is even and `y` odd, or `x` is odd and `y` even. -/
theorem parity_dichotomy (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1) :
    (x % 2 = 0 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 2 = 0) :=
  h.even_odd_of_coprime hc

/-- **Exactly one leg is even** (Even/Odd form). The two legs have opposite
parity: precisely one is even. -/
theorem exactly_one_even (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1) :
    (Even x ∧ Odd y) ∨ (Odd x ∧ Even y) := by
  rcases h.even_odd_of_coprime hc with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl ⟨Int.even_iff.mpr hx, Int.odd_iff.mpr hy⟩
  · exact Or.inr ⟨Int.odd_iff.mpr hx, Int.even_iff.mpr hy⟩

/-- The legs of a primitive triple never share parity: `Even x ↔ ¬ Even y`. -/
theorem even_iff_not_even (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1) :
    Even x ↔ ¬Even y := by
  rcases h.even_odd_of_coprime hc with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · simp [Int.even_iff, hx, hy]
  · simp [Int.even_iff, hx, hy]

/-! ## Part V: Consequence — the hypotenuse is odd

Since exactly one leg is even (`2mn`) and one odd (`m² − n²`), the hypotenuse
`z` of a primitive triple is odd: `z² = (even)² + (odd)² ≡ 1 (mod 4)`. -/

/-- The hypotenuse of a primitive Pythagorean triple is odd. -/
theorem hypotenuse_odd (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1) :
    z % 2 = 1 := by
  have he : x * x + y * y = z * z := h
  rcases h.even_odd_of_coprime hc with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · -- x even, y odd: x² ≡ 0, y² ≡ 1, so z² ≡ 1 mod 4 ⇒ z odd
    have hxx : x * x % 4 = 0 := by
      obtain ⟨k, rfl⟩ := Int.even_iff.mpr hx
      have : (k + k) * (k + k) = 4 * (k * k) := by ring
      omega
    have hyy := sq_emod_four_of_odd hy
    -- z² ≡ 1 mod 4 forces z odd (an even z would give z² ≡ 0 mod 4)
    rcases Int.emod_two_eq_zero_or_one z with hz0 | hz1
    · exfalso
      obtain ⟨k, rfl⟩ := Int.even_iff.mpr hz0
      have : (k + k) * (k + k) = 4 * (k * k) := by ring
      omega
    · exact hz1
  · have hxx := sq_emod_four_of_odd hx
    have hyy : y * y % 4 = 0 := by
      obtain ⟨k, rfl⟩ := Int.even_iff.mpr hy
      have : (k + k) * (k + k) = 4 * (k * k) := by ring
      omega
    rcases Int.emod_two_eq_zero_or_one z with hz0 | hz1
    · exfalso
      obtain ⟨k, rfl⟩ := Int.even_iff.mpr hz0
      have : (k + k) * (k + k) = 4 * (k * k) := by ring
      omega
    · exact hz1

end PythagoreanTriplesParity
