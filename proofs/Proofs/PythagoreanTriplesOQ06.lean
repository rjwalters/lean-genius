/-
  # Classification of primitive Pythagorean triples
  # (pythagorean-triples-oq-06)

  ## The Open Question

  A Pythagorean triple is a solution of x² + y² = z² in integers; it is **primitive**
  when gcd(x, y) = 1 (so the three numbers share no common factor). The classical
  classification theorem (Euclid, *Elements* Book X) says every primitive triple is,
  up to swapping the legs and signs, of the form

      x = m² − n²,   y = 2mn,   z = m² + n²

  for coprime integers m, n of opposite parity — and conversely every such (m, n)
  produces a primitive triple. This file packages both directions on top of Mathlib's
  `PythagoreanTriple.coprime_classification`, and instantiates the parametrization at
  m = 2, n = 1 to recover the smallest triple (3, 4, 5).

  ## Axiom count: 0
-/

import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

open PythagoreanTriple

namespace PythTriplesClassification

/-- **Forward direction (parametrization exists).** Every primitive Pythagorean triple
    with odd first leg `x` and positive hypotenuse `z` arises from a unique pair of
    coprime, opposite-parity integers `m ≥ 0`, `n`:

      x = m² − n²,   y = 2mn,   z = m² + n².

    This is exactly Mathlib's `coprime_classification'`. -/
theorem primitive_param {x y z : ℤ} (h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) (hodd : x % 2 = 1) (hz : 0 < z) :
    ∃ m n : ℤ, x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∧ z = m ^ 2 + n ^ 2 ∧
      Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧ 0 ≤ m :=
  h.coprime_classification' hco hodd hz

/-- **Converse direction (parametrization suffices).** For any coprime integers `m, n`
    of opposite parity, the Euclid parametrization

      (m² − n²,  2mn,  m² + n²)

    is a Pythagorean triple, and it is primitive: gcd(m² − n², 2mn) = 1. -/
theorem param_primitive (m n : ℤ) (hco : Int.gcd m n = 1)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    PythagoreanTriple (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2) ∧
      Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 :=
  (coprime_classification (x := m ^ 2 - n ^ 2) (y := 2 * m * n) (z := m ^ 2 + n ^ 2)).mpr
    ⟨m, n, Or.inl ⟨rfl, rfl⟩, Or.inl rfl, hco, hpar⟩

/-- The parametrization always solves `x² + y² = z²` (the Pythagorean identity for the
    Euclid form), with no coprimality or parity hypothesis. -/
theorem param_eq (m n : ℤ) :
    (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  ring

/-- The smallest primitive Pythagorean triple `(3, 4, 5)`, recovered from the
    parametrization at `m = 2`, `n = 1`. -/
theorem triple_3_4_5 : PythagoreanTriple 3 4 5 ∧ Int.gcd 3 4 = 1 :=
  (coprime_classification (x := 3) (y := 4) (z := 5)).mpr
    ⟨2, 1, Or.inl ⟨by norm_num, by norm_num⟩, Or.inl (by norm_num), by decide,
      Or.inl ⟨by decide, by decide⟩⟩

end PythTriplesClassification

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `primitive_param` | Every primitive triple (x odd, z > 0) is (m²−n², 2mn, m²+n²) |
  | `param_primitive` | Coprime opposite-parity (m, n) ⟹ a primitive triple |
  | `param_eq`        | (m²−n²)² + (2mn)² = (m²+n²)² (the Euclid identity) |
  | `triple_3_4_5`    | (3, 4, 5) is primitive, from m = 2, n = 1 |

  Both directions of the classification are specializations of Mathlib's
  `PythagoreanTriple.coprime_classification` / `coprime_classification'`.

  **Sorries**: 0
  **Axioms**: 0
-/
