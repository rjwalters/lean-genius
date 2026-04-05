/-
# ℤ[X,Y] and Multivariate Polynomial Rings are UFDs

OQ-01 follow-up to BezoutIdentityOQ02OQ01OQ01 (bezout-identity-oq-02-oq-01-oq-01).

The parent proof established:
- K[X] is a UFD for any field K
- R[X] is a UFD for any UFD R (Gauss's theorem)
- Irreducible ↔ prime in polynomial UFDs

This proof extends to **multivariate** polynomial rings:

  ℤ[X,Y] = (ℤ[X])[Y] is a UFD

and more generally:

  MvPolynomial σ R is a UFD for any UFD R and any fintype σ

## Proof Strategy

**Iterated Gauss**: Apply Polynomial.uniqueFactorizationMonoid twice:
1. ℤ is a UFD → ℤ[X] = Polynomial ℤ is a UFD
2. ℤ[X] is a UFD → ℤ[X][Y] = Polynomial (Polynomial ℤ) is a UFD

**Multivariate**: MvPolynomial (Fin n) R is a UFD via the typeclass instance in Mathlib,
which uses the equivalence MvPolynomial (Fin (n+1)) R ≃ MvPolynomial (Fin n) R [X].

## Tags
algebra, polynomial-rings, unique-factorization, multivariate, Gauss-lemma
-/

import Mathlib

namespace BezoutIdentityMultivarPoly

open Polynomial MvPolynomial UniqueFactorizationMonoid

/-! ## Section I: Iterated Univariate ℤ[X][Y] is a UFD -/

/-- ℤ is a UFD. -/
example : UniqueFactorizationMonoid ℤ := inferInstance

/-- ℤ[X] is a UFD (first application of Gauss's lemma). -/
example : UniqueFactorizationMonoid ℤ[X] := inferInstance

/-- ℤ[X][Y] = (ℤ[X])[Y] is a UFD (second application of Gauss's lemma). -/
theorem int_bivariate_iterated_ufd :
    UniqueFactorizationMonoid (Polynomial ℤ[X]) :=
  Polynomial.uniqueFactorizationMonoid

/-- More generally: R[X₁]···[Xₙ] is a UFD when R is a UFD. -/
theorem iterated_poly_ufd (R : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid (Polynomial (Polynomial R)) :=
  Polynomial.uniqueFactorizationMonoid

/-! ## Section II: Multivariate Polynomial Rings -/

/-- ℤ[X,Y] as a genuine bivariate polynomial ring (MvPolynomial) is a UFD. -/
theorem zxy_ufd : UniqueFactorizationMonoid (MvPolynomial (Fin 2) ℤ) :=
  inferInstance

/-- ℤ[X₁,...,Xₙ] is a UFD for any n. -/
theorem zxn_ufd (n : ℕ) : UniqueFactorizationMonoid (MvPolynomial (Fin n) ℤ) :=
  inferInstance

/-- Multivariate polynomials over any UFD, in finitely many variables, form a UFD. -/
theorem mv_poly_over_ufd_is_ufd (R σ : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Fintype σ] [DecidableEq σ] :
    UniqueFactorizationMonoid (MvPolynomial σ R) :=
  inferInstance

/-- ℚ[X,Y] is a UFD (polynomials over a field in 2 variables). -/
example : UniqueFactorizationMonoid (MvPolynomial (Fin 2) ℚ) := inferInstance

/-- K[X₁,...,Xₙ] is a UFD for any field K and any n. -/
theorem mv_poly_over_field_is_ufd (K : Type*) [Field K] (n : ℕ) :
    UniqueFactorizationMonoid (MvPolynomial (Fin n) K) :=
  inferInstance

/-! ## Section III: Irreducible = Prime in ℤ[X,Y] -/

/-- In ℤ[X,Y], irreducible ↔ prime (as in any UFD). -/
theorem zxy_irreducible_iff_prime {p : MvPolynomial (Fin 2) ℤ} :
    Irreducible p ↔ Prime p :=
  irreducible_iff_prime

/-- **Euclid's lemma for ℤ[X,Y]**: if p | f*g and p is irreducible, then p | f or p | g. -/
theorem zxy_euclid_lemma {p f g : MvPolynomial (Fin 2) ℤ}
    (hp : Irreducible p) (hdvd : p ∣ f * g) : p ∣ f ∨ p ∣ g :=
  (irreducible_iff_prime.mp hp).dvd_or_dvd hdvd

/-! ## Section IV: Irreducible Elements in ℤ[X,Y] -/

/-- X (the first variable) is irreducible in ℤ[X,Y]. -/
theorem x_irred_in_zxy : Irreducible (MvPolynomial.X (σ := Fin 2) (R := ℤ) 0) :=
  irreducible_iff_prime.mpr MvPolynomial.X_prime

/-- Y (the second variable) is irreducible in ℤ[X,Y]. -/
theorem y_irred_in_zxy : Irreducible (MvPolynomial.X (σ := Fin 2) (R := ℤ) 1) :=
  irreducible_iff_prime.mpr MvPolynomial.X_prime

/-- Any variable Xᵢ is irreducible in MvPolynomial σ R (over a UFD R). -/
theorem xi_irred_in_mv_poly {R σ : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (i : σ) :
    Irreducible (MvPolynomial.X (σ := σ) (R := R) i) :=
  irreducible_iff_prime.mpr MvPolynomial.X_prime

/-! ## Section V: Chain of Gauss Applications -/

/-- Summary: The UFD chain from ℤ up to ℤ[X₁,...,Xₙ] via iterated Gauss's lemma. -/
theorem ufd_chain_summary :
    UniqueFactorizationMonoid ℤ ∧
    UniqueFactorizationMonoid ℤ[X] ∧
    UniqueFactorizationMonoid (Polynomial ℤ[X]) ∧
    UniqueFactorizationMonoid (Polynomial (Polynomial ℤ[X])) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

-- Note: MvPolynomial (Fin 2) R ≃ₐ[R] Polynomial (Polynomial R)
-- is the formal reason why "ℤ[X,Y]" (as MvPolynomial) equals the iterated ring (ℤ[X])[Y].
-- This equivalence exists in Mathlib via MvPolynomial.finSuccEquiv applied twice.

#check @zxy_ufd
#check @mv_poly_over_ufd_is_ufd
#check @xi_irred_in_mv_poly

end BezoutIdentityMultivarPoly
