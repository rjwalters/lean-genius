/-
# Does linear_combination Scale to Gauss's Lemma?

## Open Question (bezout-identity-oq-02-oq-04)

The parent proof (BezoutIdentityOQ02) showed that Euclid's lemma for integers follows
from the `linear_combination` tactic: given gcd(a,b)=1, find x,y with a*x + b*y = 1,
then prove divisibility by algebraic manipulation.

**Question**: Does this `linear_combination` approach scale to Gauss's Lemma for
polynomial rings? Gauss's Lemma states:
1. The product of two primitive polynomials is primitive (classical form).
2. A primitive irreducible polynomial p divides g*h only if p | g or p | h.

## Answer

**PARTIALLY YES, but with an important structural shift.**

- Over a **field k**, k[X] is a Euclidean domain (PID, Bézout). The `linear_combination`
  approach works directly: coprime polynomials satisfy a Bézout identity, and the
  same algebraic manipulation as in ℤ proves divisibility.

- Over **ℤ**, ℤ[X] is a UFD but NOT a PID. The ideal ⟨2, X⟩ is not principal, so there
  is no Bézout identity for 2 and X (coprime elements). Instead, Gauss's lemma uses
  the **content** of polynomials (gcd of coefficients) and the UFD structure.
  The `linear_combination` tactic cannot directly close Gauss-type goals over ℤ.

## Key Results

1. `gauss_lemma_primitive_mul`: Product of primitives is primitive (Gauss, classical).
2. `poly_euclids_lemma_field`: Euclid analog over k via IsCoprime / linear_combination.
3. `poly_euclids_lemma_int`: Euclid analog over ℤ via UFD structure, no Bézout needed.
4. `two_X_not_coprime_in_ZX`: Witness that ℤ[X] is not Bézout (linear_combination fails).
-/

import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

namespace BezoutIdentityOQ02OQ04

open Polynomial

/-!
## Part I: Classical Gauss's Lemma

Product of primitive polynomials is primitive.
-/

/--
**Gauss's Lemma (Classical Form)**:
If f and g are primitive polynomials in R[X] (over a GCD domain R),
then f * g is also primitive.

This requires the multiplicativity of content: content(f * g) = content(f) * content(g).
The `linear_combination` tactic cannot prove this structural fact.
-/
theorem gauss_lemma_primitive_mul {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
    {f g : R[X]} (hf : f.IsPrimitive) (hg : g.IsPrimitive) : (f * g).IsPrimitive :=
  hf.mul hg

/--
**Content multiplicativity** (the engine behind Gauss's Lemma):
content(f * g) = content(f) * content(g).
-/
theorem content_multiplicative {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
    (f g : R[X]) : (f * g).content = f.content * g.content :=
  Polynomial.content_mul f g

/-!
## Part II: Euclid's Lemma Over a Field (linear_combination Works!)

Over k[X] where k is a field, the ring is a PID (hence Bézout domain).
Coprime polynomials have a Bézout identity, and `linear_combination` applies.
-/

/--
**Polynomial Euclid's Lemma Over a Field** (via IsCoprime):
If f, g ∈ k[X] are coprime and f | g*h, then f | h.

In a PID, IsCoprime is equivalent to "gcd(f,g) is a unit", so Bézout applies.
-/
theorem poly_euclids_lemma_field {k : Type*} [Field k] {f g h : k[X]}
    (hcop : IsCoprime f g) (hdvd : f ∣ g * h) : f ∣ h :=
  hcop.dvd_of_dvd_mul_left hdvd

/--
**Explicit Bézout/linear_combination proof** over a field:
The `linear_combination` tactic closes the key algebraic step.
-/
theorem poly_bezout_application {k : Type*} [Field k] {f g : k[X]}
    (hcop : IsCoprime f g) {h : k[X]} (hdvd : f ∣ g * h) : f ∣ h := by
  -- Get Bézout coefficients a, b with a*f + b*g = 1
  obtain ⟨a, b, hab⟩ := hcop
  -- Get quotient m with g*h = f*m
  obtain ⟨m, hm⟩ := hdvd
  -- Witness: h = f * (a*h + b*m), proved by linear_combination
  -- Key identity: h = (a*f + b*g)*h = a*f*h + b*g*h = a*f*h + b*f*m = f*(a*h + b*m)
  exact ⟨a * h + b * m, by linear_combination -h * hab + b * hm⟩

/-!
## Part III: Euclid's Lemma Over ℤ (UFD Structure, No Bézout)

Over ℤ[X], the Bézout approach fails. Instead: in a UFD, irreducible ↔ prime.
-/

/--
**Polynomial Euclid's Lemma Over ℤ** (via UFD):
If p ∈ ℤ[X] is irreducible and p | g*h, then p | g or p | h.

Uses: ℤ[X] is a UFD, so irreducible implies prime, and primes satisfy divisibility.
The `linear_combination` tactic plays no role here.
-/
theorem poly_euclids_lemma_int {p g h : ℤ[X]} (hirr : Irreducible p)
    (hdvd : p ∣ g * h) : p ∣ g ∨ p ∣ h := by
  have hprime : Prime p := (irreducible_iff_prime).mp hirr
  exact hprime.dvd_or_dvd hdvd

/--
**Connection to content**: If p is primitive and irreducible, it is prime in ℤ[X].
This is the polynomial analog of "prime numbers are prime elements in ℤ."
-/
theorem primitive_irreducible_is_prime {p : ℤ[X]} (hp : p.IsPrimitive) (hirr : Irreducible p) :
    Prime p :=
  (irreducible_iff_prime).mp hirr

/-!
## Part IV: ℤ[X] Is Not a Bézout Domain

The element 2 and X are coprime in the PID sense (gcd = 1 in ℚ[X]),
but there is NO Bézout identity a * 2 + b * X = 1 in ℤ[X].
This is why `linear_combination` cannot be the primary tool here.
-/

/--
**ℤ[X] is NOT a Bézout domain** (witness: 2 and X have no Bézout identity).
If a * 2 + b * X = 1 in ℤ[X], evaluate at 0: 2 * a(0) = 1, impossible in ℤ.
-/
theorem two_X_not_coprime_in_ZX : ¬ IsCoprime (2 : ℤ[X]) X := by
  intro ⟨a, b, hab⟩
  -- Evaluate both sides at x = 0
  have h := congr_arg (Polynomial.eval 0) hab
  simp [eval_mul, eval_add, eval_one, eval_X, eval_ofNat] at h
  -- h : eval 0 a * 2 = 1 in ℤ, which omega can refute
  omega

/--
**ℤ[X] is a UFD** (Mathlib provides this instance):
-/
example : UniqueFactorizationMonoid ℤ[X] := inferInstance

/-!
## Part V: Summary and Comparison

The full picture of how Euclid's lemma is proved in different rings:

| Ring  | PID? | Bézout identity? | `linear_combination`? | Proof method         |
|-------|------|------------------|----------------------|----------------------|
| ℤ     | YES  | YES              | YES (OQ02 parent)    | Bézout via IsCoprime |
| k[X]  | YES  | YES              | YES                  | Bézout via IsCoprime |
| ℤ[X]  | NO   | NO               | NO                   | UFD: irred ↔ prime   |
| R[X] UFD R | NO | NO            | NO                   | IsPrimitive.mul      |

**Conclusion**: The `linear_combination` approach scales to fields (k[X] is a PID/Bézout),
but NOT to ℤ[X]. Gauss's lemma over ℤ requires the UFD content theory.
-/

end BezoutIdentityOQ02OQ04
