import Mathlib
import Proofs.Sqrt2Minpoly

open Polynomial IntermediateField

set_option maxHeartbeats 800000

/-
# Composite-Exponent Collapse of the Radical Minimal Polynomial

**Open Question (follow-up to sqrt2-minpoly-oq-01-oq-02)**:

The parent file `Sqrt2MinpolyOQ01OQ02` proves `minpoly ℚ (√r) = X² − r` for every
nonnegative rational `r` that is not a rational square, and the companion
`Sqrt2MinpolyOQ01OQ02PrimePow` proves `minpoly ℚ (a^(1/pⁿ)) = X^(pⁿ) − a` for an odd
prime `p` and `a` not a `p`-th power. Both results say: *for a prime-power exponent the
naive monic `X^N − a` is already the minimal polynomial.*

The PrimePow docstring flags — but does not formalize — the contrast at **composite**
exponents:

> "in sharp contrast to composite exponents (`minpoly ℚ (4^(1/4)) = X² − 2`, since
> `X⁴ − 4 = (X² − 2)(X² + 2)`)."

This file formalizes that concrete witness. It demonstrates that the prime-power
restriction in the irreducibility criterion `X_pow_sub_C_irreducible_iff_of_prime_pow`
is *essential*: for the composite exponent `4`, the radical `4^(1/4)` has degree only
`2` over `ℚ`, so the naive degree-`4` polynomial `X⁴ − 4` is **not** the minimal
polynomial — it is reducible.

## Mathematical Content

The collapse is driven by a single arithmetic coincidence: `4^(1/4) = √2`. Indeed
`4 = 2²`, so the real fourth root is `(2²)^(1/4) = 2^(1/2) = √2`. Once that identity is
in hand, the entire degree-2 theory of `√2` (already machine-verified in the headline
`Sqrt2Minpoly` entry) transfers verbatim:

* `minpoly ℚ (4^(1/4)) = X² − 2`  (degree 2, **not** 4);
* `[ℚ(4^(1/4)) : ℚ] = 2`;
* `X⁴ − 4 = (X² − 2)(X² + 2)` is a genuine factorization into two non-units, so
  `X⁴ − 4` is reducible and cannot be the minimal polynomial.

This is exactly why the Kummer/Vahlen–Capelli irreducibility criterion is stated for
prime-power exponents only: a non-prime exponent can split off a lower-degree factor,
collapsing the extension.

## Status: 0 sorries, 0 axioms. Docker-verified (`Proofs.Sqrt2MinpolyOQ01OQ02Composite`,
7744 jobs). Every lemma reused from `Sqrt2Minpoly` is machine-verified, and the new
arguments are elementary `rpow` and polynomial-degree manipulations.
-/

namespace Sqrt2MinpolyOQ01OQ02Composite

/-! ## Part I: The Arithmetic Coincidence `4^(1/4) = √2` -/

/-- The real fourth root of `4` is `√2`, because `4 = 2²` forces
    `(2²)^(1/4) = 2^(1/2) = √2`. This single identity is what makes the composite
    exponent `4` collapse to the degree-2 theory of `√2`. -/
theorem four_rpow_quarter_eq_sqrt_two : (4 : ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt 2 := by
  have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    have h := Real.rpow_natCast (2 : ℝ) 2
    simp only [Nat.cast_ofNat] at h
    rw [h]; norm_num
  rw [Real.sqrt_eq_rpow,
    show (4 : ℝ) ^ ((1 : ℝ) / 4) = ((2 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 4) from by rw [h4],
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (2 : ℝ) * ((1 : ℝ) / 4) = (1 : ℝ) / 2 from by norm_num]

/-! ## Part II: The Collapse — Minimal Polynomial and Degree -/

/-- **Composite-exponent collapse**: `minpoly ℚ (4^(1/4)) = X² − 2`. The minimal
    polynomial has degree `2`, *not* the naive `4`, because `4^(1/4) = √2`. -/
theorem minpoly_four_rpow_quarter :
    minpoly ℚ ((4 : ℝ) ^ ((1 : ℝ) / 4)) = X ^ 2 - C 2 := by
  rw [four_rpow_quarter_eq_sqrt_two]
  exact Sqrt2Minpoly.minpoly_sqrt_two

/-- The algebraic degree of `4^(1/4)` over `ℚ` is `2`. -/
theorem minpoly_four_rpow_quarter_natDegree :
    (minpoly ℚ ((4 : ℝ) ^ ((1 : ℝ) / 4))).natDegree = 2 := by
  rw [four_rpow_quarter_eq_sqrt_two]
  exact Sqrt2Minpoly.sqrt_two_minpoly_natDegree

/-- **Field extension degree**: `[ℚ(4^(1/4)) : ℚ] = 2`, the degree of `ℚ(√2)`, not the
    naive `4`. -/
theorem adjoin_four_rpow_quarter_finrank :
    Module.finrank ℚ ℚ⟮(4 : ℝ) ^ ((1 : ℝ) / 4)⟯ = 2 := by
  rw [four_rpow_quarter_eq_sqrt_two]
  exact Sqrt2Minpoly.adjoin_sqrt_two_finrank

/-! ## Part III: Why the Naive `X⁴ − 4` Fails — Reducibility -/

/-- The defining factorization of the naive degree-4 candidate:
    `X⁴ − 4 = (X² − 2)(X² + 2)` over `ℚ`. -/
theorem X_pow_four_sub_four_eq :
    (X ^ 4 - C 4 : ℚ[X]) = (X ^ 2 - C 2) * (X ^ 2 + C 2) := by
  have hC : (C 4 : ℚ[X]) = C 2 * C 2 := by rw [← C_mul]; norm_num
  rw [hC]; ring

/-- `X⁴ − 4` is **not** irreducible over `ℚ`: it splits into the two degree-2
    non-units `X² − 2` and `X² + 2`. Hence it cannot be the minimal polynomial of
    `4^(1/4)` (whose minimal polynomial has degree 2). -/
theorem X_pow_four_sub_four_not_irreducible :
    ¬ Irreducible (X ^ 4 - C 4 : ℚ[X]) := by
  intro h
  rcases h.isUnit_or_isUnit X_pow_four_sub_four_eq with hu | hu
  · have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_pow_sub_C] at hd
    norm_num at hd
  · have e : (X ^ 2 + C 2 : ℚ[X]) = X ^ 2 - C (-2 : ℚ) := by
      rw [map_neg, sub_neg_eq_add]
    rw [e] at hu
    have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_pow_sub_C] at hd
    norm_num at hd

/-- The naive degree-`4` polynomial is **not** the minimal polynomial of `4^(1/4)`:
    its degree is `4`, while the true minimal polynomial has degree `2`. -/
theorem minpoly_ne_X_pow_four_sub_four :
    minpoly ℚ ((4 : ℝ) ^ ((1 : ℝ) / 4)) ≠ X ^ 4 - C 4 := by
  intro h
  have hd : (minpoly ℚ ((4 : ℝ) ^ ((1 : ℝ) / 4))).natDegree = 2 :=
    minpoly_four_rpow_quarter_natDegree
  rw [h, Polynomial.natDegree_X_pow_sub_C] at hd
  norm_num at hd

end Sqrt2MinpolyOQ01OQ02Composite
