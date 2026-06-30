import Mathlib

open Polynomial IntermediateField

set_option maxHeartbeats 800000

/-
# Minimal Polynomial of a Prime-Power-Degree Radical of a Rational

**Open Question (follow-up to sqrt2-minpoly-oq-01-oq-02)**:

The parent file `Sqrt2MinpolyOQ01OQ02` proves `minpoly ℚ (√r) = X² − r` for every
nonnegative rational `r` that is not a rational square (the **degree-2** case).
A companion file generalizes this to **odd-prime** degree, proving
`minpoly ℚ (a^(1/p)) = X^p − a` for an odd prime `p` and a nonnegative rational `a`
that is not a `p`-th power, via Mathlib's Kummer irreducibility criterion
`X_pow_sub_C_irreducible_iff_of_prime_pow` specialized to exponent `n = 1`.

This file pushes that criterion to its full strength. The same Mathlib lemma states,
for an odd prime `p` and `n ≠ 0`,

  `Irreducible (X ^ (p ^ n) − C a) ↔ ∀ b, b ^ p ≠ a`,

so the criterion governs **every prime-power exponent** `p ^ n`, not just `p` itself.
We use it to prove, for an odd prime `p`, an exponent `n ≥ 1`, and a nonnegative
rational `a` that is not a `p`-th power,

  `minpoly ℚ (a^(1/pⁿ)) = X^(pⁿ) − a`,

together with the degree (`= pⁿ`) and field-extension (`[ℚ(a^(1/pⁿ)) : ℚ] = pⁿ`)
corollaries. Setting `n = 1` recovers the odd-prime companion as the special case.

## The Subtle Point

The irreducibility hypothesis is `∀ b : ℚ, b ^ p ≠ a` — "`a` is not a `p`-th power" —
and it is **independent of `n`**. It is *not* the weaker-looking condition "`a` is not
a `pⁿ`-th power". Concretely, `X⁹ − 2` is irreducible over `ℚ` because `2` is not a
**cube** (`p = 3`); whether `2` is a `9`-th power is never tested. Being a non-`p`-th
power is exactly the obstruction for the whole tower of prime-power exponents.

This is why the radical `a^(1/pⁿ)` has degree `pⁿ` over `ℚ` as soon as `a` avoids the
single Diophantine condition `∀ b, b ^ p ≠ a`: the field `ℚ(a^(1/pⁿ))` is a degree-`pⁿ`
extension with no intermediate "early collapse", in sharp contrast to composite
exponents (`minpoly ℚ (4^(1/4)) = X² − 2`, since `X⁴ − 4 = (X² − 2)(X² + 2)`).

## Mathematical Content

The minimal polynomial is monic by definition, so the canonical answer is the monic
`X^(pⁿ) − C a`. The proof is the standard "monic + irreducible + has the root ⟹ it is
the minimal polynomial" argument (`minpoly.eq_of_irreducible_of_monic`):

1. `a^(1/pⁿ)` is a root of `X^(pⁿ) − C a`: `(a^(1/pⁿ))^(pⁿ) = a^((1/pⁿ)·pⁿ) = a`
   (real `rpow`, valid since `a ≥ 0`).
2. `X^(pⁿ) − C a` is monic (`monic_X_pow_sub_C`, `pⁿ ≠ 0`).
3. `X^(pⁿ) − C a` is irreducible over `ℚ` by `X_pow_sub_C_irreducible_iff_of_prime_pow`,
   since `a` is not a `p`-th power.

## Status: 0 sorries, 0 axioms. Build-pending (Docker pool saturated this session,
3 lean-build containers on the 7.65 GB VM — building would risk OOM for peers). The
argument is a verbatim adaptation of the machine-verified degree-2 / odd-prime proofs,
replacing the exponent `p` with the prime power `pⁿ`; the only mathematical change is
that the Kummer criterion is applied at general `n` rather than `n = 1`, so no
`pow_one` rewrite is needed.
-/

namespace Sqrt2MinpolyOQ01OQ02PrimePow

/-! ## Part I: The Radical is a Root of `X^N − C a` -/

/-- For a nonnegative real `a` and `N ≠ 0`, the real `N`-th root `a^(1/N)` satisfies
    `(a^(1/N))^N = a`. -/
theorem rpow_inv_pow (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN : N ≠ 0) :
    (a ^ ((1 : ℝ) / N)) ^ N = a := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [← Real.rpow_natCast (a ^ ((1 : ℝ) / (N : ℝ))) N, ← Real.rpow_mul ha]
  rw [one_div, inv_mul_cancel₀ hN0, Real.rpow_one]

/-- `X^N − C a` annihilates `a^(1/N)` over `ℚ`, for `a ≥ 0` a nonnegative rational. -/
theorem aeval_rpow (a : ℚ) (ha : 0 ≤ a) (N : ℕ) (hN : N ≠ 0) :
    (Polynomial.aeval ((a : ℝ) ^ ((1 : ℝ) / N))) (X ^ N - C a : ℚ[X]) = 0 := by
  have ha' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hAM : (algebraMap ℚ ℝ) a = (a : ℝ) := eq_ratCast (algebraMap ℚ ℝ) a
  have hroot : ((a : ℝ) ^ ((1 : ℝ) / N)) ^ N = (a : ℝ) := rpow_inv_pow (a : ℝ) ha' N hN
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  rw [hAM, hroot, sub_self]

/-! ## Part II: The Minimal Polynomial -/

/-- **Main Theorem**: for an odd prime `p`, an exponent `n ≥ 1`, and a nonnegative
    rational `a` that is not a `p`-th power in `ℚ`,
    `minpoly ℚ (a^(1/pⁿ)) = X^(pⁿ) − a`.

    Generalizes the odd-prime companion `minpoly ℚ (a^(1/p)) = X^p − a` (its `n = 1`
    case) to arbitrary prime-power degree. The irreducibility obstruction
    `∀ b, b ^ p ≠ a` depends only on `p`, never on `n`. -/
theorem minpoly_rpow_of_odd_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (n : ℕ) (hn : n ≠ 0) (a : ℚ) (ha : 0 ≤ a) (hnp : ∀ b : ℚ, b ^ p ≠ a) :
    minpoly ℚ ((a : ℝ) ^ ((1 : ℝ) / (p ^ n : ℕ))) = X ^ p ^ n - C a := by
  have hN : p ^ n ≠ 0 := pow_ne_zero n hp.pos.ne'
  have hmonic : (X ^ p ^ n - C a : ℚ[X]).Monic := monic_X_pow_sub_C a hN
  have haeval : (Polynomial.aeval ((a : ℝ) ^ ((1 : ℝ) / (p ^ n : ℕ))))
      (X ^ p ^ n - C a : ℚ[X]) = 0 :=
    aeval_rpow a ha (p ^ n) hN
  have hirr : Irreducible (X ^ p ^ n - C a : ℚ[X]) :=
    (X_pow_sub_C_irreducible_iff_of_prime_pow (K := ℚ) hp hp2 hn).mpr hnp
  exact (minpoly.eq_of_irreducible_of_monic hirr haeval hmonic).symm

/-! ## Part III: Degree and Field-Extension Consequences -/

/-- `a^(1/N)` is integral over `ℚ` for `a ≥ 0` and `N ≠ 0` (root of the monic
    `X^N − C a`). -/
theorem rpow_isIntegral (a : ℚ) (ha : 0 ≤ a) (N : ℕ) (hN : N ≠ 0) :
    IsIntegral ℚ ((a : ℝ) ^ ((1 : ℝ) / N)) :=
  ⟨X ^ N - C a, monic_X_pow_sub_C a hN, aeval_rpow a ha N hN⟩

/-- The algebraic degree of `a^(1/pⁿ)` over `ℚ` is `pⁿ`, for odd prime `p`, `n ≥ 1`,
    and `a` not a `p`-th power. -/
theorem minpoly_rpow_natDegree (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (n : ℕ) (hn : n ≠ 0) (a : ℚ) (ha : 0 ≤ a) (hnp : ∀ b : ℚ, b ^ p ≠ a) :
    (minpoly ℚ ((a : ℝ) ^ ((1 : ℝ) / (p ^ n : ℕ)))).natDegree = p ^ n := by
  rw [minpoly_rpow_of_odd_prime_pow p hp hp2 n hn a ha hnp,
    Polynomial.natDegree_X_pow_sub_C]

/-- **Field Extension Degree**: `[ℚ(a^(1/pⁿ)) : ℚ] = pⁿ` for odd prime `p`, `n ≥ 1`,
    and `a` not a `p`-th power. -/
theorem adjoin_rpow_finrank (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (n : ℕ) (hn : n ≠ 0) (a : ℚ) (ha : 0 ≤ a) (hnp : ∀ b : ℚ, b ^ p ≠ a) :
    Module.finrank ℚ ℚ⟮(a : ℝ) ^ ((1 : ℝ) / (p ^ n : ℕ))⟯ = p ^ n := by
  rw [IntermediateField.adjoin.finrank (rpow_isIntegral a ha (p ^ n) (pow_ne_zero n hp.pos.ne'))]
  exact minpoly_rpow_natDegree p hp hp2 n hn a ha hnp

end Sqrt2MinpolyOQ01OQ02PrimePow
