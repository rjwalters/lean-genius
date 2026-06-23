import Mathlib

/-
Unique Factorization in Polynomial Rings (bezout-identity-oq-02-oq-01-oq-01)

Open question from BezoutIdentityOQ02OQ01 (FTA from Euclid's lemma):
Adapt the FTA uniqueness argument to polynomial ring unique factorization.

**Main Results**:
1. Polynomial rings over UFDs are UFDs: `UniqueFactorizationMonoid R[X]` (Mathlib)
2. Polynomial rings over fields are Euclidean domains (polynomial division)
3. Polynomial Bézout identity: if gcd(f,g) = 1 over a field, ∃ a b, a*f + b*g = 1
4. Irreducible ↔ prime in polynomial UFDs (Euclid's lemma for polynomials)

**Connection to BezoutIdentityOQ02OQ01**:
- The same Bézout → Euclid's Lemma → UFD argument works for R[X]
- Over ℤ: unique factorization into primes (FTA)
- Over K[X] (K a field): unique factorization into irreducible polynomials

**Status**: 0 sorries, 0 axioms. All results from Mathlib.
-/

open Polynomial UniqueFactorizationMonoid

namespace BezoutIdentityPolyUFD

/-!
## Section I: Polynomial Ring UFD Structure (from Mathlib)
-/

/-- **Polynomial rings over UFDs are UFDs** (Gauss's Lemma generalization).
    In particular, K[X] is a UFD for any field K. -/
example (K : Type*) [Field K] : UniqueFactorizationMonoid K[X] := inferInstance

/-- **Polynomial rings over fields are Euclidean domains**.
    The division algorithm for polynomials gives the Euclidean structure. -/
noncomputable example (K : Type*) [Field K] : EuclideanDomain K[X] := inferInstance

/-- Over a UFD, the polynomial ring is also a UFD. -/
example (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[X] :=
  Polynomial.uniqueFactorizationMonoid

/-!
## Section II: Irreducible ↔ Prime (Euclid's Lemma for Polynomials)
-/

/-- **Polynomial Euclid's Lemma**: In a polynomial UFD, irreducible = prime.
    This is the generalization of Euclid's lemma from ℤ to polynomial rings. -/
theorem poly_irreducible_iff_prime {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {p : R[X]} :
    Irreducible p ↔ Prime p :=
  UniqueFactorizationMonoid.irreducible_iff_prime

/-- If p is irreducible in K[X] and p | f*g, then p | f or p | g.
    This is Euclid's lemma for polynomial rings over fields. -/
theorem poly_euclid_lemma {K : Type*} [Field K] {p f g : K[X]}
    (hp : Irreducible p) (hdvd : p ∣ f * g) : p ∣ f ∨ p ∣ g :=
  (irreducible_iff_prime.mp hp).dvd_or_dvd hdvd

/-!
## Section III: Polynomial Bézout Identity
-/

/-- **Polynomial Bézout Identity**: If gcd(f, g) = 1 over a field K,
    then there exist polynomials a, b ∈ K[X] such that a*f + b*g = 1.
    This is the polynomial analogue of the integer Bézout identity. -/
theorem poly_bezout {K : Type*} [Field K] (f g : K[X])
    (hcop : IsCoprime f g) : ∃ a b : K[X], a * f + b * g = 1 := hcop

/-- **IsCoprime via Bézout**: Coprimeness is equivalent to the existence of
    Bézout coefficients. -/
theorem poly_isCoprime_iff {K : Type*} [Field K] (f g : K[X]) :
    IsCoprime f g ↔ ∃ a b : K[X], a * f + b * g = 1 := Iff.rfl


/-!
## Section IV: Unique Factorization Theorem for Polynomials
-/

/-- **Existence of irreducible factors**: Every non-constant polynomial over a field
    has an irreducible factor. -/
theorem poly_has_irred_factor {K : Type*} [Field K] (f : K[X]) (hf : f.natDegree ≠ 0) :
    ∃ p : K[X], Irreducible p ∧ p ∣ f :=
  Polynomial.exists_irreducible_of_natDegree_ne_zero hf

/-- **Unique factorization exists**: K[X] is a UFD, so every nonzero polynomial
    has a factorization into irreducibles (abstract existence via typeclass). -/
theorem poly_ufd_structure (K : Type*) [Field K] :
    UniqueFactorizationMonoid K[X] := inferInstance

/-!
## Section V: Concrete Examples over ℚ
-/

/-- x² - 1 factors as (x - 1)(x + 1) in ℚ[X]. -/
example : (Polynomial.X ^ 2 - 1 : ℚ[X]) = (Polynomial.X - 1) * (Polynomial.X + 1) := by ring

/-- x is irreducible in ℚ[X]. -/
theorem x_irreducible_Q : Irreducible (Polynomial.X : ℚ[X]) :=
  Polynomial.irreducible_X

/-- x² - 1 is reducible in ℚ[X]: it factors as (x-1)(x+1). -/
theorem x_sq_sub_one_reducible : ¬ Irreducible ((Polynomial.X ^ 2 - 1 : ℚ[X])) := by
  intro hirr
  have h : (Polynomial.X ^ 2 - 1 : ℚ[X]) = (Polynomial.X - 1) * (Polynomial.X + 1) := by ring
  rcases hirr.isUnit_or_isUnit h with hu | hu
  · -- X - 1 = X - C 1 is irreducible (monic linear), hence not a unit
    have heq : (Polynomial.X - (1 : ℚ[X])) = Polynomial.X - Polynomial.C 1 := by simp
    exact (Polynomial.irreducible_X_sub_C (1 : ℚ)).1 (heq ▸ hu)
  · -- X + 1 = X - C(-1) is irreducible (monic linear), hence not a unit
    have heq : (Polynomial.X + (1 : ℚ[X])) = Polynomial.X - Polynomial.C (-1) := by
      simp [Polynomial.C_neg, sub_neg_eq_add]
    exact (Polynomial.irreducible_X_sub_C (-1 : ℚ)).1 (heq ▸ hu)

/-!
## Section VI: Parallel with Integer FTA
-/

/-- **Parallel Summary**: The same abstract proof structure (Bézout → Euclid → UFD)
    works for both ℤ and K[X]:

    For ℤ (BezoutIdentityOQ02OQ01):
      ∃ x y : ℤ, gcd(a,b)*1 = a*x + b*y → p | ab → p | a or p | b → FTA

    For K[X] (this file):
      ∃ a b : K[X], a*f + b*g = 1 → p | fg → p | f or p | g → poly-FTA

    In both cases: the ring is a Euclidean domain → GCDMonoid → UFD. -/
theorem bezout_parallel {K : Type*} [Field K] (p f g : K[X])
    (hirr : Irreducible p) (hdvd : p ∣ f * g) : p ∣ f ∨ p ∣ g :=
  (irreducible_iff_prime.mp hirr).dvd_or_dvd hdvd

/-!
## Section VII: GCD Structure (requires DecidableEq for explicit gcd)
-/

/-- The polynomial GCD divides both arguments. -/
theorem poly_gcd_dvd_both {K : Type*} [Field K] [DecidableEq K] (f g : K[X]) :
    EuclideanDomain.gcd f g ∣ f ∧ EuclideanDomain.gcd f g ∣ g :=
  ⟨EuclideanDomain.gcd_dvd_left f g, EuclideanDomain.gcd_dvd_right f g⟩

/-- The polynomial GCD is a linear combination (Bézout's identity for K[X]).
    Note: EuclideanDomain.gcd_eq_gcd_ab has the form gcd = f * gcdA + g * gcdB
    which we rewrite via commutativity to gcd = gcdA * f + gcdB * g. -/
theorem poly_gcd_bezout_form {K : Type*} [Field K] [DecidableEq K] (f g : K[X]) :
    ∃ a b : K[X],
      EuclideanDomain.gcd f g = a * f + b * g :=
  ⟨EuclideanDomain.gcdA f g, EuclideanDomain.gcdB f g, by
    rw [EuclideanDomain.gcd_eq_gcd_ab]; ring⟩

end BezoutIdentityPolyUFD
