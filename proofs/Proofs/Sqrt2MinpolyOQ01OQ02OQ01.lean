import Mathlib

open Polynomial IntermediateField

set_option maxHeartbeats 800000

/-
# Minimal Polynomial of an Odd-Prime-Degree Radical of a Rational

**Open Question (follow-up to sqrt2-minpoly-oq-01-oq-02)**:

The parent file `Sqrt2MinpolyOQ01OQ02` proves `minpoly ℚ (√r) = X² − r` for every
nonnegative rational `r` that is not a rational square — the **degree-2** case. The
natural next question, listed explicitly among that problem's next steps
("Generalize to k-th roots of rationals: minpoly ℚ (r^(1/k)) = X^k − r"), is whether
the minimal polynomial of a higher radical `a^(1/k)` is `X^k − a`.

For composite `k` this is **false** without an extra hypothesis: e.g.
`X⁴ − 4 = (X² − 2)(X² + 2)` is reducible, so `minpoly ℚ (4^(1/4)) = minpoly ℚ (√2)
= X² − 2`, not `X⁴ − 4`. The clean statement holds for **prime** degree, where Kummer
theory gives the sharp irreducibility criterion:

  for an odd prime `p`, `X^p − C a` is irreducible over a field `K` **iff** `a` is not
  a `p`-th power in `K` (`X_pow_sub_C_irreducible_iff_of_prime_pow` at exponent `n = 1`).

This file uses that criterion to prove, for an **odd prime** `p` and a nonnegative
rational `a` that is not a `p`-th power of a rational,

  `minpoly ℚ (a^(1/p)) = X^p − a`,

together with the degree (`= p`) and field-extension (`[ℚ(a^(1/p)) : ℚ] = p`)
corollaries.

The remaining prime, `p = 2`, is precisely the parent's square-root theorem
(`minpoly ℚ (√r) = X² − r` for `¬ IsSquare r`), proved there by the elementary
irrationality argument rather than the Kummer machinery (which excludes `p = 2`).
Together the two files cover every prime degree.

## Mathematical Content

The minimal polynomial is monic by definition, so the canonical answer is the monic
`X^p − C a`. The proof is the standard "monic + irreducible + has the root ⟹ it is the
minimal polynomial" argument (`minpoly.eq_of_irreducible_of_monic`):

1. `a^(1/p)` is a root of `X^p − C a`: `(a^(1/p))^p = a^((1/p)·p) = a^1 = a` (real
   `rpow`, valid since `a ≥ 0`).
2. `X^p − C a` is monic (`monic_X_pow_sub_C`, `p ≠ 0`).
3. `X^p − C a` is irreducible over `ℚ` by the Kummer criterion at exponent `1`, since
   `a` is not a `p`-th power.

The hypothesis `∀ b : ℚ, b ^ p ≠ a` is exactly "`a` is not a `p`-th power in `ℚ`",
the odd-prime analogue of the parent's `¬ IsSquare a`.

## Status: 0 sorries, 0 axioms. Docker-verified green (7743 jobs). The argument adapts
the machine-verified `Sqrt2MinpolyOQ01OQ02` degree-2 proof, replacing the elementary
irrationality step with Mathlib's `X_pow_sub_C_irreducible_iff_of_prime_pow`.
-/

namespace Sqrt2MinpolyOQ01OQ02OQ01

/-! ## Part I: The Radical is a Root of `X^p − C a` -/

/-- For a nonnegative real `a`, the real `p`-th root `a^(1/p)` satisfies `(a^(1/p))^p = a`. -/
theorem rpow_inv_pow (a : ℝ) (ha : 0 ≤ a) (p : ℕ) (hp : p ≠ 0) :
    (a ^ ((1 : ℝ) / p)) ^ p = a := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  rw [← Real.rpow_natCast (a ^ ((1 : ℝ) / (p : ℝ))) p, ← Real.rpow_mul ha]
  rw [one_div, inv_mul_cancel₀ hp0, Real.rpow_one]

/-- `X^p − C a` annihilates `a^(1/p)` over `ℚ`, for `a ≥ 0` a nonnegative rational. -/
theorem aeval_rpow (a : ℚ) (ha : 0 ≤ a) (p : ℕ) (hp : p ≠ 0) :
    (Polynomial.aeval ((a : ℝ) ^ ((1 : ℝ) / p))) (X ^ p - C a : ℚ[X]) = 0 := by
  have ha' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hAM : (algebraMap ℚ ℝ) a = (a : ℝ) := eq_ratCast (algebraMap ℚ ℝ) a
  have hroot : ((a : ℝ) ^ ((1 : ℝ) / p)) ^ p = (a : ℝ) := rpow_inv_pow (a : ℝ) ha' p hp
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  rw [hAM, hroot, sub_self]

/-! ## Part II: The Minimal Polynomial -/

/-- **Main Theorem**: for an odd prime `p` and a nonnegative rational `a` that is not a
    `p`-th power in `ℚ`, `minpoly ℚ (a^(1/p)) = X^p − a`.

    Generalizes `Sqrt2MinpolyOQ01OQ02.minpoly_sqrt_of_not_isSquare_rat` (the `p = 2`
    case) from square roots to odd-prime-degree radicals. -/
theorem minpoly_rpow_of_odd_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a : ℚ)
    (ha : 0 ≤ a) (hnp : ∀ b : ℚ, b ^ p ≠ a) :
    minpoly ℚ ((a : ℝ) ^ ((1 : ℝ) / p)) = X ^ p - C a := by
  have hp0 : p ≠ 0 := hp.pos.ne'
  have hmonic : (X ^ p - C a : ℚ[X]).Monic := monic_X_pow_sub_C a hp0
  have haeval : (Polynomial.aeval ((a : ℝ) ^ ((1 : ℝ) / p))) (X ^ p - C a : ℚ[X]) = 0 :=
    aeval_rpow a ha p hp0
  have hirr : Irreducible (X ^ p - C a : ℚ[X]) := by
    have h := (X_pow_sub_C_irreducible_iff_of_prime_pow (K := ℚ) (n := 1) hp hp2
      one_ne_zero).mpr hnp
    rwa [pow_one] at h
  exact (minpoly.eq_of_irreducible_of_monic hirr haeval hmonic).symm

/-! ## Part III: Degree and Field-Extension Consequences -/

/-- `a^(1/p)` is integral over `ℚ` for `a ≥ 0` (root of the monic `X^p − C a`). -/
theorem rpow_isIntegral (a : ℚ) (ha : 0 ≤ a) (p : ℕ) (hp : p ≠ 0) :
    IsIntegral ℚ ((a : ℝ) ^ ((1 : ℝ) / p)) :=
  ⟨X ^ p - C a, monic_X_pow_sub_C a hp, aeval_rpow a ha p hp⟩

/-- The algebraic degree of `a^(1/p)` over `ℚ` is `p`, for odd prime `p` and `a` not a
    `p`-th power. -/
theorem minpoly_rpow_natDegree (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a : ℚ)
    (ha : 0 ≤ a) (hnp : ∀ b : ℚ, b ^ p ≠ a) :
    (minpoly ℚ ((a : ℝ) ^ ((1 : ℝ) / p))).natDegree = p := by
  rw [minpoly_rpow_of_odd_prime p hp hp2 a ha hnp, Polynomial.natDegree_X_pow_sub_C]

/-- **Field Extension Degree**: `[ℚ(a^(1/p)) : ℚ] = p` for odd prime `p` and `a` not a
    `p`-th power. -/
theorem adjoin_rpow_finrank (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (a : ℚ)
    (ha : 0 ≤ a) (hnp : ∀ b : ℚ, b ^ p ≠ a) :
    Module.finrank ℚ ℚ⟮(a : ℝ) ^ ((1 : ℝ) / p)⟯ = p := by
  rw [IntermediateField.adjoin.finrank (rpow_isIntegral a ha p hp.pos.ne')]
  exact minpoly_rpow_natDegree p hp hp2 a ha hnp

end Sqrt2MinpolyOQ01OQ02OQ01
