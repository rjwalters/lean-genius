import Mathlib

/-
# GCDMonoid Normalization on k[X] — the Monic Representative

## Research Problem
gcd-algorithm-oq-04-oq-01 (extension of gcd-algorithm-oq-04)

## What This Proves

Over a field `k`, the polynomial ring `k[X]` carries a canonical
`NormalizationMonoid` structure. The abstract `normalize` map and its unit
`normUnit` are not opaque: they are exactly "make it monic". Concretely, for a
nonzero polynomial `p`:

  * `normUnit p  = C (leadingCoeff p)⁻¹`              (a constant unit)
  * `normalize p = C (leadingCoeff p)⁻¹ * p`          (the monic associate)
  * `normalize p` is monic, and it is the **unique** monic polynomial
    associated to `p`.

As a consequence, the canonical gcd in `k[X]` — i.e. the *normalized* associate
of the Euclidean-algorithm gcd — is monic (or `0`), which is exactly the monic
gcd every textbook algorithm returns.

The parent entry (`gcd-algorithm-oq-04`) established the coherence between the
`EuclideanDomain` gcd and the `GCDMonoid` gcd and their normalization. This entry
pins down the *concrete* form of that normalization on `k[X]`.

## Key Mathlib Facts Used

- `Polynomial.coe_normUnit_of_ne_zero` — over a field, `↑(normUnit p) = C (leadingCoeff p)⁻¹`.
- `normalize_apply` — `normalize x = x * ↑(normUnit x)`.
- `Polynomial.monic_normalize` — `normalize p` is monic for `p ≠ 0`.
- `Polynomial.normalize_eq_self_iff_monic`, `Polynomial.Monic.normalize_eq_self`.
- `normalize_eq_normalize_iff_associated`, `normalize_associated`.

## Axiom Count
0 axioms, 0 sorries.
-/

namespace GcdAlgorithmOQ04OQ01

open Polynomial

variable {k : Type*} [Field k] [DecidableEq k]

/-! ## Part I: The normalization unit is the inverse leading coefficient

In a `NormalizationMonoid`, `normUnit x` is the unit witnessing that
`normalize x` is the canonical associate of `x`. For `k[X]` over a field, this
unit is the *constant* polynomial whose value is the inverse leading coefficient.
-/

/-- The normalization unit of a nonzero polynomial over a field is the constant
polynomial of the inverse leading coefficient. -/
theorem normUnit_eq_C_inv_leadingCoeff {p : k[X]} (hp : p ≠ 0) :
    (↑(normUnit p) : k[X]) = C (leadingCoeff p)⁻¹ :=
  coe_normUnit_of_ne_zero hp

/-! ## Part II: `normalize` is "divide by the leading coefficient"

This is the headline identity: the abstract normalized associate of `p` is the
explicit monic polynomial obtained by scaling `p` by `(leadingCoeff p)⁻¹`.
-/

/-- **Headline.** Over a field, the normalized associate of a nonzero polynomial
is the monic polynomial `(leadingCoeff p)⁻¹ • p`, written with `C`. -/
theorem normalize_eq_C_inv_leadingCoeff_mul {p : k[X]} (hp : p ≠ 0) :
    normalize p = C (leadingCoeff p)⁻¹ * p := by
  rw [normalize_apply, normUnit_eq_C_inv_leadingCoeff hp, mul_comm]

/-- The `p = 0` convention: `normalize 0 = 0` (and `leadingCoeff 0 = 0`). -/
theorem normalize_zero_poly : normalize (0 : k[X]) = 0 := normalize_zero

/-! ## Part III: The normalized associate is monic -/

/-- The normalized associate of a nonzero polynomial is monic. -/
theorem monic_normalize_poly {p : k[X]} (hp : p ≠ 0) : (normalize p).Monic :=
  monic_normalize hp

/-- The leading coefficient of `normalize p` is `1` when `p ≠ 0`
(an equivalent restatement of monicity). -/
theorem leadingCoeff_normalize_eq_one {p : k[X]} (hp : p ≠ 0) :
    leadingCoeff (normalize p) = 1 :=
  monic_normalize_poly hp

/-- `normalize p` is associated to `p`: it has the same divisors. -/
theorem normalize_associated_poly (p : k[X]) : Associated (normalize p) p :=
  normalize_associated p

/-! ## Part IV: `normalize p` is the *unique* monic associate

`normalize` selects the canonical representative of the associate class; over a
field that representative is the unique monic one. We record both the
characterization `normalize p = p ↔ p.Monic` and the uniqueness statement.
-/

/-- Characterization: a nonzero polynomial equals its own normalization iff it is
already monic. -/
theorem normalize_eq_self_iff {p : k[X]} (hp : p ≠ 0) :
    normalize p = p ↔ p.Monic :=
  normalize_eq_self_iff_monic hp

/-- **Uniqueness.** Any monic polynomial associated to `p` is exactly `normalize p`.
Combined with `monic_normalize_poly` and `normalize_associated_poly`, this says
`normalize p` is *the* monic associate of `p`. -/
theorem eq_normalize_of_monic_associated {p q : k[X]}
    (hq : q.Monic) (h : Associated p q) : q = normalize p := by
  have hpq : normalize p = normalize q := normalize_eq_normalize_iff_associated.2 h
  rw [hpq, hq.normalize_eq_self]

/-- Existence-and-uniqueness packaged: for `p ≠ 0` there is a unique monic
polynomial associated to `p`, namely `normalize p`. -/
theorem exists_unique_monic_associate {p : k[X]} (hp : p ≠ 0) :
    ∃! m : k[X], m.Monic ∧ Associated m p := by
  refine ⟨normalize p, ⟨monic_normalize_poly hp, normalize_associated_poly p⟩, ?_⟩
  rintro m ⟨hm, hassoc⟩
  exact eq_normalize_of_monic_associated hm (hassoc.symm)

/-! ## Part V: The canonical gcd over a field is monic

`EuclideanDomain.gcd` runs the Euclidean algorithm but need not return a monic
result. The *canonical* gcd is its normalized associate, `normalize (gcd p q)`,
which is the monic gcd. We work with the `GCDMonoid` coming from
`EuclideanDomain.gcdMonoid` (a `def`, brought in via `letI`, exactly as in the
parent entry), so that `GCDMonoid.gcd = EuclideanDomain.gcd`.
-/

/-- The normalized Euclidean gcd of two polynomials over a field is monic whenever
it is nonzero — i.e. the canonical gcd is the monic gcd. -/
theorem monic_normalize_gcd {p q : k[X]}
    (hpq : EuclideanDomain.gcd p q ≠ 0) :
    (normalize (EuclideanDomain.gcd p q)).Monic :=
  monic_normalize hpq

/-- Explicit monic form of the canonical gcd: it is `(leadingCoeff g)⁻¹ • g`
where `g = EuclideanDomain.gcd p q`. -/
theorem normalize_gcd_eq {p q : k[X]} (hpq : EuclideanDomain.gcd p q ≠ 0) :
    normalize (EuclideanDomain.gcd p q)
      = C (leadingCoeff (EuclideanDomain.gcd p q))⁻¹ * EuclideanDomain.gcd p q :=
  normalize_eq_C_inv_leadingCoeff_mul hpq

/-- The canonical (monic) gcd is associated to the Euclidean gcd, hence divides
both arguments and is a true gcd. -/
theorem normalize_gcd_dvd_left (p q : k[X]) :
    normalize (EuclideanDomain.gcd p q) ∣ p :=
  (normalize_associated_poly _).dvd.trans (EuclideanDomain.gcd_dvd_left p q)

theorem normalize_gcd_dvd_right (p q : k[X]) :
    normalize (EuclideanDomain.gcd p q) ∣ q :=
  (normalize_associated_poly _).dvd.trans (EuclideanDomain.gcd_dvd_right p q)

/-- Universal property of the canonical gcd: any common divisor divides it. -/
theorem dvd_normalize_gcd {p q d : k[X]} (hp : d ∣ p) (hq : d ∣ q) :
    d ∣ normalize (EuclideanDomain.gcd p q) :=
  (EuclideanDomain.dvd_gcd hp hq).trans (associated_normalize _).dvd

/-! ## Part VI: Worked examples over ℚ -/

/-- A monic polynomial is its own normalization. -/
example : normalize (X + C 1 : ℚ[X]) = X + C 1 :=
  (monic_X_add_C (1 : ℚ)).normalize_eq_self

/-- The scalar multiple `C 2 * X` normalizes to the monic `X`. -/
example : normalize (C 2 * X : ℚ[X]) = X := by
  have hp : (C 2 * X : ℚ[X]) ≠ 0 := by
    apply mul_ne_zero
    · simp
    · exact X_ne_zero
  rw [normalize_eq_C_inv_leadingCoeff_mul hp, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_X, ← mul_assoc, ← C_mul]
  have h2 : ((2 : ℚ) * 1)⁻¹ * 2 = 1 := by norm_num
  rw [h2, C_1, one_mul]

end GcdAlgorithmOQ04OQ01
