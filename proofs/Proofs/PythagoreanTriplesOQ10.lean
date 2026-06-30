/-
Hypotenuse of a Primitive Pythagorean Triple is ≡ 1 (mod 4)

Source: Open question pythagorean-triples-oq-10 from the pythagorean-triples gallery
Status: VERIFIED (0 axioms, 0 sorries)

For a primitive Pythagorean triple `x² + y² = z²` with coprime legs and positive
hypotenuse `z`, the hypotenuse satisfies `z ≡ 1 (mod 4)` (and in particular `z` is
odd).

This *sharpens* the sibling result `PythagoreanTriplesOQ07.hypotenuse_odd`, which
only establishes `z % 2 = 1`. The two are genuinely different in strength: oddness
already follows from `z² = x² + y² ≡ 1 (mod 4)`, but that congruence is blind to
whether `z ≡ 1` or `z ≡ 3 (mod 4)` — both odd residues square to `1`. Pinning the
residue down to `1` requires the actual parametrization

    z = m² + n²,   m, n coprime of opposite parity,

supplied by Mathlib's `PythagoreanTriple.isPrimitiveClassified_of_coprime_of_pos`.
With `m, n` of opposite parity one of `m², n²` is `0 (mod 4)` and the other is
`1 (mod 4)`, so their sum — and hence `z` — is `1 (mod 4)`.

The positivity hypothesis `0 < z` is essential: it selects the positive square
root `z = +(m² + n²)` over `z = -(m² + n²)` (the latter would give `z ≡ 3`).

Structural consequence: no integer `≡ 3 (mod 4)` is ever the hypotenuse of a
primitive triple (e.g. `3, 7, 11, 19, …` are excluded), recorded below as
`not_primitive_hypotenuse_of_three_mod_four`.
-/

import Mathlib

namespace PythagoreanTriplesOQ10

open PythagoreanTriple

variable {x y z : ℤ}

/-! ## Part I: Squares modulo 4

The two arithmetic facts behind the result: an even square is `0 (mod 4)` and an
odd square is `1 (mod 4)`. -/

/-- An even integer squared is `0 (mod 4)`. -/
theorem sq_emod_four_of_even {a : ℤ} (ha : a % 2 = 0) : a ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ := Int.even_iff.mpr ha
  have h : (k + k) ^ 2 = 4 * k ^ 2 := by ring
  omega

/-- An odd integer squared is `1 (mod 4)`. -/
theorem sq_emod_four_of_odd {a : ℤ} (ha : a % 2 = 1) : a ^ 2 % 4 = 1 := by
  obtain ⟨k, rfl⟩ := Int.odd_iff.mpr ha
  have h : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
  omega

/-! ## Part II: The hypotenuse is `1 (mod 4)`

We extract the primitive parametrization `x = m² − n², y = 2mn` (or the legs
swapped), deduce `z² = (m² + n²)²`, use `0 < z` to take the positive root
`z = m² + n²`, and finish with the mod-4 squares from Part I. -/

/-- **Main result.** The hypotenuse of a primitive Pythagorean triple with `0 < z`
satisfies `z ≡ 1 (mod 4)`. -/
theorem hypotenuse_one_mod_four (h : PythagoreanTriple x y z)
    (hc : Int.gcd x y = 1) (hz : 0 < z) : z % 4 = 1 := by
  obtain ⟨m, n, hxy, -, hpar⟩ := h.isPrimitiveClassified_of_coprime_of_pos hc hz
  have he : x * x + y * y = z * z := h
  -- In either leg-ordering the Pythagorean identity gives z² = (m² + n²)².
  have hsq : z * z = (m ^ 2 + n ^ 2) * (m ^ 2 + n ^ 2) := by
    rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · subst hx; subst hy; linear_combination -he
    · subst hx; subst hy; linear_combination -he
  -- z and m² + n² are both ≥ 0 with equal squares, so they are equal.
  have hw0 : (0 : ℤ) ≤ m ^ 2 + n ^ 2 := by positivity
  have hfac : (z - (m ^ 2 + n ^ 2)) * (z + (m ^ 2 + n ^ 2)) = 0 := by
    linear_combination hsq
  have hzeq : z = m ^ 2 + n ^ 2 := by
    rcases mul_eq_zero.mp hfac with h1 | h2
    · linarith
    · linarith
  rw [hzeq]
  -- m, n have opposite parity: one square is 0 mod 4, the other 1 mod 4.
  rcases hpar with ⟨hme, hno⟩ | ⟨hmo, hne⟩
  · have h1 := sq_emod_four_of_even hme
    have h2 := sq_emod_four_of_odd hno
    omega
  · have h1 := sq_emod_four_of_odd hmo
    have h2 := sq_emod_four_of_even hne
    omega

/-! ## Part III: Consequences -/

/-- The hypotenuse of a primitive Pythagorean triple (with `0 < z`) is odd. This
is the weaker statement `PythagoreanTriplesOQ07.hypotenuse_odd`, recovered here as
an immediate corollary of the sharper mod-4 result. -/
theorem hypotenuse_odd (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1)
    (hz : 0 < z) : z % 2 = 1 := by
  have := hypotenuse_one_mod_four h hc hz
  omega

/-- **Structural consequence.** No integer `≡ 3 (mod 4)` is the hypotenuse of a
primitive Pythagorean triple. Concretely, `3, 7, 11, 19, 23, …` never occur as a
primitive hypotenuse. -/
theorem not_primitive_hypotenuse_of_three_mod_four
    (h : PythagoreanTriple x y z) (hc : Int.gcd x y = 1) (hz : 0 < z) :
    z % 4 ≠ 3 := by
  have := hypotenuse_one_mod_four h hc hz
  omega

/-- The smallest primitive triple `(3, 4, 5)`: its hypotenuse `5 ≡ 1 (mod 4)`. -/
theorem example_3_4_5 :
    PythagoreanTriple 3 4 5 ∧ Int.gcd 3 4 = 1 ∧ (5 : ℤ) % 4 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold PythagoreanTriple; norm_num
  · decide
  · decide

/-- `(20, 21, 29)`, a primitive triple with both legs large: `29 ≡ 1 (mod 4)`. -/
theorem example_20_21_29 :
    PythagoreanTriple 20 21 29 ∧ Int.gcd 20 21 = 1 ∧ (29 : ℤ) % 4 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold PythagoreanTriple; norm_num
  · decide
  · decide

end PythagoreanTriplesOQ10
