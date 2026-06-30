import Mathlib

open Polynomial Real

set_option maxHeartbeats 800000

/-
# Minimal Polynomial of √2 + √3 + √5 over ℚ

## Main Result

The minimal polynomial of α = √2 + √3 + √5 over ℚ is (a divisor of)

  p(X) = X⁸ − 40X⁶ + 352X⁴ − 960X² + 576.

This file *computes* the candidate octic and verifies its defining structural
properties.  It is the n = 3 analogue of the sister entry
`sqrt2-plus-sqrt3-irrational-oq-03`, which handles n = 2 (the quartic
X⁴ − 10X² + 1).

## How the coefficients are obtained — the Galois-conjugate product

p(X) is, by construction, the product over the eight sign-conjugates

  p(X) = ∏_{(ε₁,ε₂,ε₃) ∈ {±1}³} (X − ε₁√2 − ε₂√3 − ε₃√5).

Because the product ranges over a full set of sign flips, every cross term
involving an *odd* power of a surd cancels, leaving rational coefficients and
only even powers of X.  Computing the elementary symmetric functions of the
eight roots (equivalently, the power sums via Newton's identities) gives

  e₂ = −40, e₄ = 352, e₆ = −960, e₈ = 576,   e₁ = e₃ = e₅ = e₇ = 0,

hence p(X) = X⁸ − 40X⁶ + 352X⁴ − 960X² + 576.

## Proof strategy for the root witness

Rather than expand the eight-fold product, we verify p(α) = 0 directly by the
classical "isolate a surd and square" chain, which needs only the *squares*
of the radicals (never their signs):

1. With a = √2, b = √3, c = √5 and t = bc = √15,
   (a+b+c)² − 2a(a+b+c) = 6 + 2t.            ── isolates √2
2. Squaring,  ((a+b+c)² − 6 − 2t)² = 8(a+b+c)².
3. A single `linear_combination` over the relations of step 2 and t² = 15
   collapses to p(a+b+c) = 0.

Because steps 1–3 use only a² = 2, b² = 3, c² = 5 (and never the signs of
a, b, c), the **same** computation proves that *all eight* sign-conjugates
ε₁√2 + ε₂√3 + ε₃√5 are roots of p — exactly the Galois-conjugate family above
(`conjugates_are_roots`).

## What is and is not established here

Fully verified (0 sorries, 0 axioms):
- p annihilates α and every sign-conjugate (`conjugates_are_roots`,
  `aeval_minpoly_candidate`);
- p is monic of degree 8 (`cand_monic`, `cand_natDegree`);
- α is integral over ℚ (`sqrt_sum_isIntegral`);
- the genuine minimal polynomial divides p (`minpoly_dvd_cand`);
- *conditional* on irreducibility of p, minpoly ℚ α = p
  (`minpoly_eq_of_irreducible`).

NOT established here: irreducibility of p over ℚ (equivalently
[ℚ(√2+√3+√5):ℚ] = 8).  Unlike the n = 2 quartic — where a finite rational/
quadratic-factor analysis settles it — the degree-8 case reduces to the
multiquadratic field-degree fact, which is the parent entry's open question
oq-04 and is beyond the current Mathlib API.  We therefore expose the
minimal-polynomial identity as a theorem with irreducibility as an explicit
hypothesis rather than over-claiming a full verification.

## Status: 0 sorries, 0 axioms (irreducibility left as an explicit hypothesis)
-/

namespace Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ03

/-! ## Part I: The Galois-conjugate root family

A single computation, valid for any real square roots of 2, 3, 5 regardless of
sign, shows that all eight conjugates `ε₁√2 + ε₂√3 + ε₃√5` are roots of the
candidate octic. -/

/-- **Conjugate root family.**  For any reals `a, b, c` with `a² = 2`, `b² = 3`,
`c² = 5`, the sum `a + b + c` is a root of
`X⁸ − 40X⁶ + 352X⁴ − 960X² + 576`.

Taking `a ∈ {±√2}`, `b ∈ {±√3}`, `c ∈ {±√5}` yields all eight Galois
conjugates of `√2 + √3 + √5`. -/
theorem conjugates_are_roots (a b c : ℝ) (ha : a ^ 2 = 2) (hb : b ^ 2 = 3)
    (hc : c ^ 2 = 5) :
    (a + b + c) ^ 8 - 40 * (a + b + c) ^ 6 + 352 * (a + b + c) ^ 4
      - 960 * (a + b + c) ^ 2 + 576 = 0 := by
  -- t = bc = √15, with t² = 15
  have ht : (b * c) ^ 2 = 15 := by rw [mul_pow, hb, hc]; norm_num
  -- Step 1 + 2: isolate √2 and square it away.
  have E2 : ((a + b + c) ^ 2 - 6 - 2 * (b * c)) ^ 2 = 8 * (a + b + c) ^ 2 := by
    have hlin : (a + b + c) ^ 2 - 6 - 2 * (b * c) = 2 * a * (a + b + c) := by
      linear_combination -ha + hb + hc
    rw [hlin]
    linear_combination (4 * (a + b + c) ^ 2) * ha
  -- Step 3: collapse to p(a+b+c) = 0.
  linear_combination
    ((a + b + c) ^ 4 - 20 * (a + b + c) ^ 2 + 96 + 4 * (b * c) * ((a + b + c) ^ 2 - 6)) * E2
    + (-4 * ((a + b + c) ^ 4 - 20 * (a + b + c) ^ 2 + 96)
        - 16 * (b * c) * ((a + b + c) ^ 2 - 6)
        + 16 * ((a + b + c) ^ 2 - 6) ^ 2) * ht

/-! ## Part II: The candidate annihilates α = √2 + √3 + √5 -/

/-- **Root witness.**  `√2 + √3 + √5` is a root of
`X⁸ − 40X⁶ + 352X⁴ − 960X² + 576` over ℚ. -/
theorem aeval_minpoly_candidate :
    Polynomial.aeval (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5)
      (X ^ 8 - 40 * X ^ 6 + 352 * X ^ 4 - 960 * X ^ 2 + 576 : ℚ[X]) = 0 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_X]
  exact conjugates_are_roots _ _ _ h2 h3 h5

/-! ## Part III: Monicity, degree and integrality -/

/-- The candidate octic is monic. -/
theorem cand_monic :
    (X ^ 8 - 40 * X ^ 6 + 352 * X ^ 4 - 960 * X ^ 2 + 576 : ℚ[X]).Monic := by
  monicity!

/-- The candidate octic has degree 8. -/
theorem cand_natDegree :
    (X ^ 8 - 40 * X ^ 6 + 352 * X ^ 4 - 960 * X ^ 2 + 576 : ℚ[X]).natDegree = 8 := by
  compute_degree!

/-- `√2 + √3 + √5` is integral over ℚ: the candidate octic is a monic
annihilating polynomial. -/
theorem sqrt_sum_isIntegral :
    IsIntegral ℚ (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) :=
  ⟨_, cand_monic, aeval_minpoly_candidate⟩

/-! ## Part IV: Relation to the genuine minimal polynomial -/

/-- The minimal polynomial of `√2 + √3 + √5` over ℚ divides the candidate
octic.  (Always true, since the candidate is a nonzero annihilator.) -/
theorem minpoly_dvd_cand :
    minpoly ℚ (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5)
      ∣ (X ^ 8 - 40 * X ^ 6 + 352 * X ^ 4 - 960 * X ^ 2 + 576 : ℚ[X]) :=
  minpoly.dvd ℚ _ aeval_minpoly_candidate

/-- **Minimal polynomial, conditional on irreducibility.**  If the candidate
octic is irreducible over ℚ, then it *is* the minimal polynomial of
`√2 + √3 + √5`.

Irreducibility here is equivalent to `[ℚ(√2+√3+√5):ℚ] = 8`, the multiquadratic
field-degree fact recorded as open question oq-04 of the parent entry; it is
not yet available in Mathlib, so it is left as an explicit hypothesis rather
than discharged. -/
theorem minpoly_eq_of_irreducible
    (hirr : Irreducible (X ^ 8 - 40 * X ^ 6 + 352 * X ^ 4 - 960 * X ^ 2 + 576 : ℚ[X])) :
    minpoly ℚ (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5)
      = (X ^ 8 - 40 * X ^ 6 + 352 * X ^ 4 - 960 * X ^ 2 + 576 : ℚ[X]) :=
  (minpoly.eq_of_irreducible_of_monic hirr aeval_minpoly_candidate cand_monic).symm

end Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ03
