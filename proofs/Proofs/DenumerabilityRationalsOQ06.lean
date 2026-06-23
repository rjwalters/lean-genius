import Mathlib

/-!
# Denumerability of Rationals OQ-06: the polynomial ring `ℚ[X]` is countable

The base entry and its siblings show the *rationals* are denumerable, and OQ-05
extends this to finite products, lists and finite subsets of `ℚ` (`#(ℚ × ℚ)`,
`#(List ℚ)`, `#(Finset ℚ)`), all of which stay at `ℵ₀`, while `ℕ → ℚ` jumps to the
continuum `𝔠`. None of those touch the object that actually drives *algebraic*
countability: the polynomial ring.

This entry records that `ℚ[X]` — and `ℤ[X]` — is countably infinite:

`#(ℚ[X]) = ℵ₀`  and  `#(ℤ[X]) = ℵ₀`,

so there is an explicit bijection `ℕ ≃ ℚ[X]`. The proof is one application of
Mathlib's `Polynomial.cardinalMk_eq_max` (`#(R[X]) = max #R ℵ₀` for a nontrivial
semiring `R`): with `#ℚ = #ℤ = ℵ₀` the maximum collapses to `ℵ₀`.

Countability of `ℚ[X]` is the cardinal fact behind the countability of the algebraic
numbers (a single algebraic number is a root of some polynomial in `ℚ[X]`, and each
polynomial has finitely many roots); OQ-07 pursues that consequence explicitly.

No axioms beyond Lean's foundational core, no sorries.
-/

namespace DenumerabilityRationalsOQ06

open Cardinal Polynomial

/-- **`#ℚ = ℵ₀`.** The rationals are countable and infinite, hence exactly `ℵ₀`. -/
theorem mk_rat : #ℚ = ℵ₀ := mk_eq_aleph0 ℚ

/-- **`#(ℚ[X]) = ℵ₀`.** By `Polynomial.cardinalMk_eq_max`, `#(ℚ[X]) = max #ℚ ℵ₀`;
since `#ℚ = ℵ₀`, the maximum is `max ℵ₀ ℵ₀ = ℵ₀`. -/
theorem cardinalMk_polynomial_rat : #(ℚ[X]) = ℵ₀ := by
  rw [Polynomial.cardinalMk_eq_max, mk_rat, max_self]

/-- **`#(ℤ[X]) = ℵ₀`.** Same argument with `#ℤ = ℵ₀` (`Cardinal.mk_int`). -/
theorem cardinalMk_polynomial_int : #(ℤ[X]) = ℵ₀ := by
  rw [Polynomial.cardinalMk_eq_max, mk_int, max_self]

/-- The rational and integer polynomial rings have the same cardinality. -/
theorem cardinalMk_polynomial_rat_eq_int : #(ℚ[X]) = #(ℤ[X]) := by
  rw [cardinalMk_polynomial_rat, cardinalMk_polynomial_int]

/-- **`ℚ[X]` is denumerable**: `#ℕ = #(ℚ[X])` (both are `ℵ₀`), so there is a
bijection `ℕ ≃ ℚ[X]`. -/
theorem nonempty_nat_equiv_polynomial_rat : Nonempty (ℕ ≃ ℚ[X]) :=
  Cardinal.eq.mp (by rw [mk_nat, cardinalMk_polynomial_rat])

/-- An explicit (noncomputable) enumeration of `ℚ[X]` by the naturals, extracted from
the cardinal equality. -/
noncomputable def natEquivPolynomialRat : ℕ ≃ ℚ[X] :=
  (nonempty_nat_equiv_polynomial_rat).some

end DenumerabilityRationalsOQ06
