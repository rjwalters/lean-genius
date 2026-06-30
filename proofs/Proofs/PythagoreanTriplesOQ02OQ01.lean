/-
  Pythagorean Triples: Complete Classification via Gaussian Integers

  Open Question (pythagorean-triples-oq-02-oq-01), a sub-question of
  `pythagorean-triples-oq-02` (Gaussian integers):

  "Can the *classification* of all primitive Pythagorean triples be formalized?
   Every primitive triple has the form (m²-n², 2mn, m²+n²) with gcd(m,n)=1 and
   opposite parity.  This uses the UFD property of ℤ[i]."

  The Gaussian-integer story behind the parametrization (developed in the parent
  entry) is: squaring z = m + n·i gives

        z² = (m² - n²) + (2mn)·i,        N(z²) = N(z)² = (m² + n²)²,

  so the two legs (m²-n², 2mn) are the real/imaginary parts of z², and the
  hypotenuse m²+n² is the Gaussian norm N(z).  This file connects that
  parametrization map to the full classification.

  Mathlib already proves the deep direction — that *every* primitive triple
  arises this way — in `PythagoreanTriple.coprime_classification` (whose proof
  rests on ℤ[i] being a UFD / the gcd theory of the integers).  We therefore
  present this entry honestly as a **bridge**: the elementary forward facts
  (the parametrization always yields a primitive triple) are proved here, and
  the full biconditional classification is exported and packaged in the
  Gaussian-parametrization language.

  Tags: number-theory, gaussian-integers, pythagorean-triples, classification
-/

import Mathlib

namespace PythagoreanTriplesOQ02OQ01

open Int

/-! ## The Gaussian-square parametrization -/

/-- The parametrization map `(m, n) ↦ (m²-n², 2mn, m²+n²)`.  The first two
components are the real and imaginary parts of the Gaussian square
`(m + n·i)²`, and the third is the Gaussian norm `N(m + n·i) = m²+n²`. -/
def paramTriple (m n : ℤ) : ℤ × ℤ × ℤ := (m ^ 2 - n ^ 2, 2 * m * n, m ^ 2 + n ^ 2)

/-- The parametrization always produces a Pythagorean triple — the algebraic
heart, i.e. `N(z²) = N(z)²` written out: `(m²-n²)² + (2mn)² = (m²+n²)²`. -/
theorem paramTriple_isPythagorean (m n : ℤ) :
    PythagoreanTriple (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2) := by
  delta PythagoreanTriple; ring

/-- Constructive (easy) direction of the classification: a coprime pair of
opposite parity yields a **primitive** Pythagorean triple, i.e. the two legs
`m²-n²` and `2mn` are coprime.

(We derive coprimality from Mathlib's `coprime_classification` rather than the
private lemma `coprime_sq_sub_mul`; the point here is the Gaussian framing.) -/
theorem paramTriple_isPrimitive {m n : ℤ} (co : Int.gcd m n = 1)
    (pp : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 :=
  (PythagoreanTriple.coprime_classification
      (x := m ^ 2 - n ^ 2) (y := 2 * m * n) (z := m ^ 2 + n ^ 2)).mpr
    ⟨m, n, Or.inl ⟨rfl, rfl⟩, Or.inl rfl, co, pp⟩ |>.2

/-! ## The complete classification (bridge to Mathlib) -/

/-- **Complete classification of primitive Pythagorean triples**, packaged in
the Gaussian-parametrization language.  An integer triple `(x, y, z)` is a
primitive Pythagorean triple iff it arises from the parametrization map for some
coprime, opposite-parity pair `(m, n)` (up to swapping the legs and the sign of
`z`).

The hard direction — every primitive triple has this shape — is
`PythagoreanTriple.coprime_classification`, ultimately a consequence of unique
factorization in ℤ[i]. -/
theorem primitive_classification {x y z : ℤ} :
    (PythagoreanTriple x y z ∧ Int.gcd x y = 1) ↔
      ∃ m n,
        (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
          (z = m ^ 2 + n ^ 2 ∨ z = -(m ^ 2 + n ^ 2)) ∧
            Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :=
  PythagoreanTriple.coprime_classification

/-- The sharper "standard form" when the odd leg `x` is taken positive and `z`
is positive: there exist `m ≥ 0` and `n` with exactly
`x = m²-n²,  y = 2mn,  z = m²+n²`, coprime and of opposite parity.  This is the
textbook parametrization with no sign/order ambiguity. -/
theorem primitive_classification_pos {x y z : ℤ} (h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) (hodd : x % 2 = 1) (hpos : 0 < z) :
    ∃ m n, x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∧ z = m ^ 2 + n ^ 2 ∧
      Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧ 0 ≤ m :=
  h.coprime_classification' hco hodd hpos

/-- A clean number-theoretic corollary: the hypotenuse of any positive primitive
Pythagorean triple (with odd leg `x`) is a sum of two squares, `z = m² + n²`.
This is the Gaussian-integer fact `z = N(m + n·i)` made explicit. -/
theorem hypotenuse_sum_of_squares {x y z : ℤ} (h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) (hodd : x % 2 = 1) (hpos : 0 < z) :
    ∃ m n, z = m ^ 2 + n ^ 2 := by
  obtain ⟨m, n, _, _, hz, _⟩ := primitive_classification_pos h hco hodd hpos
  exact ⟨m, n, hz⟩

end PythagoreanTriplesOQ02OQ01
