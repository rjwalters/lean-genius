/-
  GCD Complete Characterization in Euclidean Domains (OQ-04-OQ-02)

  Source: bezout-identity-oq-04-oq-02
  Status: PROVED (0 sorries, 0 axioms)

  **Question**: Can `gcd_complete_characterization` from BezoutIdentityOQ04.lean
  be generalized beyond ℕ/ℤ using Mathlib's algebraic hierarchy?

  **Answer**: YES — for any Euclidean domain.

  The Bezout property `gcd(a,b) = a*x + b*y` holds in any Euclidean domain via
  `EuclideanDomain.gcd_eq_gcd_ab`. This yields the ideal characterization:
    ∃ x y : R, a * x + b * y = c  ↔  gcd(a, b) ∣ c

  The correct generalization requires `EuclideanDomain` (or `IsBezout`), NOT merely
  `UniqueFactorizationDomain`: ℤ[x] is a UFD but gcd(2, x) = 1 yet 1 ∉ {2f + xg}.
-/

import Mathlib

namespace BezoutIdentityOQ04OQ02

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

open EuclideanDomain

/-!
## Part I: Core Lemmas
-/

/-- In any Euclidean domain, gcd(a, b) divides every linear combination a*x + b*y. -/
theorem gcd_dvd_linear_combination (a b x y : R) :
    gcd a b ∣ a * x + b * y :=
  dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left a b) x)
           (dvd_mul_of_dvd_left (gcd_dvd_right a b) y)

/-- **Bezout's Identity in a Euclidean domain**:
    gcd(a, b) is a linear combination of a and b. -/
theorem gcd_achievable_ED (a b : R) :
    ∃ x y : R, a * x + b * y = gcd a b :=
  ⟨gcdA a b, gcdB a b, (gcd_eq_gcd_ab a b).symm⟩

/-!
## Part II: Main Characterization
-/

/-- **Generalized Bezout (OQ-04-OQ-02)**:
    In any Euclidean domain, `c` is a linear combination of `a` and `b`
    if and only if `gcd(a, b)` divides `c`. -/
theorem linear_combination_iff_gcd_dvd (a b c : R) :
    (∃ x y : R, a * x + b * y = c) ↔ gcd a b ∣ c := by
  constructor
  · rintro ⟨x, y, rfl⟩
    exact gcd_dvd_linear_combination a b x y
  · rintro ⟨k, hk⟩
    -- Bezout: gcd a b = a * gcdA a b + b * gcdB a b
    -- So c = gcd * k = (a * gcdA + b * gcdB) * k = a * (gcdA * k) + b * (gcdB * k)
    exact ⟨gcdA a b * k, gcdB a b * k, by
      calc a * (gcdA a b * k) + b * (gcdB a b * k)
          = (a * gcdA a b + b * gcdB a b) * k := by ring
        _ = gcd a b * k := by rw [← gcd_eq_gcd_ab]
        _ = c := hk.symm⟩

/-- **Complete GCD characterization in a Euclidean domain** (cf. OQ-04 for ℤ):
    d satisfies achievability and universality iff d and gcd(a, b) divide each other. -/
theorem gcd_complete_characterization_ED (a b d : R) :
    ((∃ x y : R, a * x + b * y = d) ∧
     (∀ c : R, (∃ x y : R, a * x + b * y = c) → d ∣ c))
    ↔ (d ∣ gcd a b ∧ gcd a b ∣ d) := by
  simp_rw [linear_combination_iff_gcd_dvd]
  constructor
  · intro ⟨h_achieve, h_divides⟩
    exact ⟨h_divides _ (dvd_refl _), h_achieve⟩
  · intro ⟨hd_gcd, hgcd_d⟩
    exact ⟨hgcd_d, fun c hc => dvd_trans hd_gcd hc⟩

/-!
## Part III: Corollaries
-/

/-- gcd(a, b) itself satisfies both achievability and universality. -/
theorem gcd_characterizes_ideal (a b : R) :
    (∃ x y : R, a * x + b * y = gcd a b) ∧
    (∀ c : R, (∃ x y : R, a * x + b * y = c) → gcd a b ∣ c) :=
  (gcd_complete_characterization_ED a b (gcd a b)).mpr ⟨dvd_refl _, dvd_refl _⟩

/-- Every Euclidean domain is a Bezout domain. -/
instance : IsBezout R := inferInstance

/-!
## Part IV: Examples in ℤ
-/

/-- gcd(6, 15) = 3, and 3 = 6*(-2) + 15*1 (Bezout coefficients). -/
example : ∃ x y : ℤ, 6 * x + 15 * y = 3 := ⟨-2, 1, by norm_num⟩

/-- 3 | 6, so 6 is achievable from {6, 15}. -/
example : ∃ x y : ℤ, 6 * x + 15 * y = 6 := ⟨1, 0, by norm_num⟩

/-- 4 is NOT achievable from {6, 15}: gcd(6, 15) = 3 and 3 ∤ 4. -/
example : ¬ ∃ x y : ℤ, 6 * x + 15 * y = 4 := by
  rintro ⟨x, y, h⟩; omega

/-- gcd(7, 5) = 1: every integer is a linear combination of 7 and 5.
    Bezout coefficients: 7 * 3 + 5 * (-4) = 1. -/
example (c : ℤ) : ∃ x y : ℤ, 7 * x + 5 * y = c := ⟨3 * c, -4 * c, by ring⟩

/-- In ℤ[X] (polynomial ring over ℤ): gcd(X^2 - 1, X - 1) involves Euclidean structure.
    Witness: (X^2 - 1) * 0 + (X - 1) * 1 = X - 1. -/
example : ∃ p q : Polynomial ℤ,
    (Polynomial.X ^ 2 - 1) * p + (Polynomial.X - 1) * q = (Polynomial.X - 1) :=
  ⟨0, 1, by ring⟩

/-!
## Summary
-/

/-
OQ-04-OQ-02 is **resolved** (0 axioms, 0 sorries):

**Answer**: YES — `gcd_complete_characterization` generalizes to Euclidean domains.

Key results:
- `linear_combination_iff_gcd_dvd`: ∃ x y, a*x + b*y = c ↔ gcd(a,b) | c
  (works in any Euclidean domain via Bezout's identity gcd_eq_gcd_ab)
- `gcd_complete_characterization_ED`: d and gcd(a,b) divide each other
  iff d satisfies achievability + universality
- `gcd_characterizes_ideal`: gcd(a,b) always satisfies both conditions

Why NOT just UFD: ℤ[x] is a UFD, gcd(2, x) = 1, but 1 ∉ {2f + xg | f,g ∈ ℤ[x]}.
The correct abstraction is EuclideanDomain (or IsBezout domain).
-/

#check @linear_combination_iff_gcd_dvd
#check @gcd_complete_characterization_ED

end BezoutIdentityOQ04OQ02
