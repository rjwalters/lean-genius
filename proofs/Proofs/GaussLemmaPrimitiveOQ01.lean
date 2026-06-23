/-
Gauss's Lemma: a primitive integer polynomial is irreducible over ℤ iff over ℚ

Source: Open question from the gauss-lemma gallery family
Status: VERIFIED (0 axioms, 0 sorries)

**Gauss's Lemma** (irreducibility form) states that for a *primitive* polynomial
`p ∈ ℤ[X]` — one whose coefficients share no common prime factor — irreducibility
over ℤ is equivalent to irreducibility of its image in ℚ[X]:

      p primitive  ⟹  ( Irreducible p  ↔  Irreducible (p over ℚ) ).

Mathlib provides this as `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`
(in `Mathlib/RingTheory/Polynomial/GaussLemma.lean`), but the gallery had no
entry assembling the statement together with the two facts that give it teeth:

  * the **monic specialization**, where primitivity is automatic, so the
    biconditional holds with no side condition; and
  * a **worked witness that primitivity is essential** — the non-primitive
    polynomial `2X`, which is *reducible* over ℤ yet *irreducible* over ℚ.

We package all three.

We prove:
1. `gauss_lemma_int`        — the biconditional for a primitive `p : ℤ[X]`
2. `gauss_lemma_int_monic`  — the unconditional biconditional for monic `p`
3. `two_mul_X_not_primitive`     — `2X` is not primitive (content 2)
4. `two_mul_X_reducible_over_int`— `2X = (C 2)·X` is reducible over ℤ
5. `two_mul_X_irreducible_over_rat` — its image `2X` is irreducible over ℚ (degree 1)
6. `primitivity_necessary`   — the existential tying 3–5 together: there is a
   polynomial reducible over ℤ but irreducible over ℚ, hence non-primitive, so
   the primitivity hypothesis of Gauss's Lemma cannot be dropped.
-/

import Mathlib

open Polynomial

namespace GaussLemmaPrimitiveOQ01

/-- **Gauss's Lemma over ℤ.** A *primitive* integer polynomial is irreducible over
ℤ if and only if its image in ℚ[X] is irreducible. This is the headline of the
entry; the proof is Mathlib's `IsPrimitive.Int.irreducible_iff_irreducible_map_cast`. -/
theorem gauss_lemma_int {p : ℤ[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (Int.castRingHom ℚ)) :=
  IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp

/-- **Monic specialization.** A monic polynomial is automatically primitive
(`Monic.isPrimitive`), so for monic `p : ℤ[X]` irreducibility over ℤ and over ℚ
coincide with no extra hypothesis — the most useful everyday form of Gauss's Lemma
(e.g. for checking irreducibility of a monic integer polynomial by working over ℚ). -/
theorem gauss_lemma_int_monic {p : ℤ[X]} (hp : p.Monic) :
    Irreducible p ↔ Irreducible (p.map (Int.castRingHom ℚ)) :=
  IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp.isPrimitive

/-- The polynomial `2X = (C 2)·X` is **not primitive**: `C 2` divides it but `2` is
not a unit of ℤ, so its coefficients share the common factor `2`. -/
theorem two_mul_X_not_primitive : ¬ (C 2 * X : ℤ[X]).IsPrimitive := by
  intro h
  have h2 : IsUnit (2 : ℤ) :=
    (isPrimitive_iff_isUnit_of_C_dvd.mp h) 2 (dvd_mul_right (C 2) X)
  simp [Int.isUnit_iff] at h2

/-- `2X` is **reducible over ℤ**: it factors as `(C 2)·X` with neither factor a
unit (`C 2` is not a unit because `2` is not a unit of ℤ; `X` is not a unit because
it has positive degree). -/
theorem two_mul_X_reducible_over_int : ¬ Irreducible (C 2 * X : ℤ[X]) := by
  intro hirr
  rcases hirr.isUnit_or_isUnit rfl with h | h
  · -- `IsUnit (C 2)` would make `2` a unit of ℤ
    rw [Polynomial.isUnit_C, Int.isUnit_iff] at h
    omega
  · -- `IsUnit X` would force `natDegree X = 0`, but it is `1`
    have := Polynomial.natDegree_eq_zero_of_isUnit h
    simp [Polynomial.natDegree_X] at this

/-- The image of `2X` in ℚ[X] is `2X`, which is **irreducible over ℚ**: it has
degree one over a field. -/
theorem two_mul_X_irreducible_over_rat :
    Irreducible ((C 2 * X : ℤ[X]).map (Int.castRingHom ℚ)) := by
  apply Polynomial.irreducible_of_degree_eq_one
  rw [Polynomial.degree_map_eq_of_injective (Int.castRingHom ℚ).injective_int]
  compute_degree!

/-- **Primitivity is essential.** There is an integer polynomial — namely `2X` —
that is reducible over ℤ yet irreducible over ℚ, and it fails to be primitive.
Hence the primitivity hypothesis in `gauss_lemma_int` genuinely cannot be removed:
without it the irreducibility biconditional is false. -/
theorem primitivity_necessary :
    ∃ p : ℤ[X], ¬ Irreducible p ∧ Irreducible (p.map (Int.castRingHom ℚ)) ∧
      ¬ p.IsPrimitive :=
  ⟨C 2 * X, two_mul_X_reducible_over_int, two_mul_X_irreducible_over_rat,
    two_mul_X_not_primitive⟩

end GaussLemmaPrimitiveOQ01
