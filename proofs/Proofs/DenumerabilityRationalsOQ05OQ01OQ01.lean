/-
# Denumerability of the Rationals OQ-05-OQ-01-OQ-01:
# countability and cardinality of multivariate polynomial and monoid algebras

## Open Question
The parent (`denumerability-rationals-oq-05-oq-01`) proved the `ℵ₀/𝔠` dichotomy for the
univariate polynomial ring over any countably infinite commutative ring `R`:
`#(R[X]) = ℵ₀` while `#(ℕ → R) = 𝔠`. Its first listed open question asks to
**generalise the polynomial side** to

  * several variables — `#(R[X₁, …, Xₙ]) = ℵ₀`, and
  * monoid algebras — `#(MonoidAlgebra R M) = ℵ₀` for countable `R` and countable `M`.

This entry settles both. The phenomenon is purely a statement about countable building
blocks: as a *type*, both algebras are finitely supported families over countable index
sets, so they are countable; combined with an evident infinitude they pin to exactly `ℵ₀`.

## Approach
Both algebras are, by definition, `Finsupp` types:

  * `MvPolynomial σ R = AddMonoidAlgebra R (σ →₀ ℕ) = ((σ →₀ ℕ) →₀ R)`, and
  * `MonoidAlgebra R M = (M →₀ R)`.

**Countability.** `Finsupp` of countable types over a countable codomain is countable
(`Finsupp.instCountable`, the same engine the parent used for `ℕ →₀ R`). For the
multivariate case this fires *twice*: `σ →₀ ℕ` is countable (countable `σ`, countable `ℕ`),
hence `(σ →₀ ℕ) →₀ R` is countable.

**Infinitude.** A coefficient embedding injects `R` (assumed infinite):
`MvPolynomial.C : R → MvPolynomial σ R` is injective, and `r ↦ single m₀ r` injects `R`
into `MonoidAlgebra R M` once `M` is nonempty.

**Cardinality.** A countable infinite type has cardinality exactly `ℵ₀`
(`Cardinal.mk_eq_aleph0`). So `#(MvPolynomial σ R) = ℵ₀ = #(MonoidAlgebra R M)`, and passing
to either algebra leaves the cardinality unchanged: `= #R`.

Sorry-free and axiom-free.
-/
import Mathlib

namespace DenumerabilityRationalsOQ05OQ01OQ01

open Cardinal

variable {R : Type} {σ : Type} {M : Type}

/-! ### Multivariate polynomials -/

/-- **`MvPolynomial σ R` is countable** whenever the coefficient ring `R` and the variable
index `σ` are countable. Unfolding `MvPolynomial σ R = AddMonoidAlgebra R (σ →₀ ℕ)
= ((σ →₀ ℕ) →₀ R)`, the `Finsupp` countability instance fires twice: first to make the
exponent space `σ →₀ ℕ` countable, then to make the coefficient family `(σ →₀ ℕ) →₀ R`
countable. -/
theorem countable_mvPolynomial [CommRing R] [Countable R] [Countable σ] :
    Countable (MvPolynomial σ R) :=
  inferInstanceAs (Countable ((σ →₀ ℕ) →₀ R))

/-- **`MvPolynomial σ R` is infinite** when the coefficient ring `R` is infinite. The
constant-polynomial embedding `MvPolynomial.C : R → MvPolynomial σ R` is injective, so it
transports `Infinite R` to the polynomial algebra (valid for any variable set `σ`, even
empty). -/
theorem infinite_mvPolynomial [CommRing R] [Infinite R] :
    Infinite (MvPolynomial σ R) :=
  Infinite.of_injective _ (MvPolynomial.C_injective σ R)

/-- **`#(MvPolynomial σ R) = ℵ₀`** for any countably infinite ring `R` and countable variable
set `σ`. The algebra is countable and infinite, so `Cardinal.mk_eq_aleph0` pins its
cardinality at exactly `ℵ₀`: adjoining countably many commuting indeterminates never leaves
denumerability. This is the multivariate generalisation of the parent's `#(R[X]) = ℵ₀`. -/
theorem mk_mvPolynomial [CommRing R] [Countable R] [Infinite R] [Countable σ] :
    #(MvPolynomial σ R) = ℵ₀ := by
  haveI : Countable (MvPolynomial σ R) := countable_mvPolynomial
  haveI : Infinite (MvPolynomial σ R) := infinite_mvPolynomial
  exact mk_eq_aleph0 _

/-- **Passing to a polynomial algebra in countably many variables does not change the
cardinality: `#(MvPolynomial σ R) = #R`.** Both sides equal `ℵ₀` (the right via
`mk_eq_aleph0` on the countably infinite `R`). The algebra is a strictly larger ring but the
same size set. -/
theorem mk_mvPolynomial_eq_mk [CommRing R] [Countable R] [Infinite R] [Countable σ] :
    #(MvPolynomial σ R) = #R := by
  rw [mk_mvPolynomial, mk_eq_aleph0 R]

/-! ### Monoid algebras -/

/-- **`MonoidAlgebra R M` is countable** whenever the coefficient ring `R` and the monoid `M`
are countable. By definition `MonoidAlgebra R M = (M →₀ R)`, a finitely supported family over
countable types, so the same `Finsupp` countability engine applies. (Only the *type*
structure is used, so no algebraic hypotheses on `M` are required.) -/
theorem countable_monoidAlgebra [Semiring R] [Countable R] [Countable M] :
    Countable (MonoidAlgebra R M) :=
  inferInstanceAs (Countable (M →₀ R))

/-- **`MonoidAlgebra R M` is infinite** when the coefficient ring `R` is infinite and the
index `M` is nonempty. Fixing any point `m₀ : M`, the single-support embedding
`r ↦ single m₀ r` injects `R` into `MonoidAlgebra R M`, transporting `Infinite R`. -/
theorem infinite_monoidAlgebra [Semiring R] [Infinite R] [Nonempty M] :
    Infinite (MonoidAlgebra R M) := by
  obtain ⟨m₀⟩ := ‹Nonempty M›
  have h : Infinite (M →₀ R) :=
    Infinite.of_injective (fun r : R => Finsupp.single m₀ r)
      (fun a b hab => by simpa using DFunLike.congr_fun hab m₀)
  exact h

/-- **`#(MonoidAlgebra R M) = ℵ₀`** for any countably infinite ring `R` and countable
nonempty index `M`. Countable and infinite, hence exactly `ℵ₀` by `Cardinal.mk_eq_aleph0`:
the monoid-algebra generalisation of the parent's `#(R[X]) = ℵ₀` (recovered at `M = ℕ`, where
`MonoidAlgebra R ℕ = R[X]`). -/
theorem mk_monoidAlgebra [Semiring R] [Countable R] [Infinite R] [Countable M] [Nonempty M] :
    #(MonoidAlgebra R M) = ℵ₀ := by
  haveI : Countable (MonoidAlgebra R M) := countable_monoidAlgebra
  haveI : Infinite (MonoidAlgebra R M) := infinite_monoidAlgebra
  exact mk_eq_aleph0 _

/-- **`#(MonoidAlgebra R M) = #R`.** Both sides are `ℵ₀`. -/
theorem mk_monoidAlgebra_eq_mk
    [Semiring R] [Countable R] [Infinite R] [Countable M] [Nonempty M] :
    #(MonoidAlgebra R M) = #R := by
  rw [mk_monoidAlgebra, mk_eq_aleph0 R]

/-! ### Concrete instances -/

/-- **`#(MvPolynomial ℕ ℚ) = ℵ₀`.** Rational polynomials in countably many variables remain
denumerable. -/
theorem mk_mvPolynomial_nat_rat : #(MvPolynomial ℕ ℚ) = ℵ₀ :=
  mk_mvPolynomial

/-- **`#(MvPolynomial (Fin 3) ℤ) = ℵ₀`.** Integer polynomials in three variables are
denumerable. -/
theorem mk_mvPolynomial_fin_int : #(MvPolynomial (Fin 3) ℤ) = ℵ₀ :=
  mk_mvPolynomial

/-- **`#(MonoidAlgebra ℚ ℕ) = ℵ₀`.** The rational monoid algebra over `(ℕ, +)` — which *is*
`ℚ[X]` — is denumerable, recovering the parent's univariate result through the monoid-algebra
route. -/
theorem mk_monoidAlgebra_nat_rat : #(MonoidAlgebra ℚ ℕ) = ℵ₀ :=
  mk_monoidAlgebra

end DenumerabilityRationalsOQ05OQ01OQ01
