/-
# Bounded Prime Gaps OQ04-OQ03:
# The Gauss Sum Bound |τ(χ)| = √p (Prime Modulus, from Mathlib)

Source: Research session, July 2026 (researcher-1)

## The Question

OQ04-OQ02 catalogs six "minimal Mathlib additions" needed for the
Bombieri-Vinogradov theorem. The first and most tractable of these is

  **Addition 1 (`gaussSumBound`)** — for a primitive Dirichlet character
  χ mod q, the Gauss sum τ(χ) = Σ_t χ(t)·e(t/q) has |τ(χ)| = √q.

That catalog records `gaussSumBound` as an *axiom*. This file asks: how
much of it is already provable from current Mathlib (v4.26.0), and where
exactly is the genuine gap?

## The Answer

The **prime-modulus case is fully provable from Mathlib** with no axioms.
For a prime p and a nontrivial Dirichlet character χ mod p,

  ‖gaussSum χ stdAddChar‖ = √p .

The proof combines two existing Mathlib results:

1. `gaussSum_mul_gaussSum_eq_card` : for χ ≠ 1 and ψ primitive over a
   **field** R, `gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = #R`.
2. Conjugation: over ℂ, `conj (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹` because
   `conj (χ a) = χ⁻¹ a` (`MulChar.star_apply'`) and `conj (ψ a) = ψ⁻¹ a`
   (the standard additive character is unit-circle valued).

Together `gaussSum χ ψ · conj (gaussSum χ ψ) = p`, i.e. `‖τ(χ)‖² = p`.

## Where the Gap Really Is

Mathlib's `gaussSum_mul_gaussSum_eq_card` requires `[Field R]`. For
`R = ZMod q` this holds **iff q is prime**. The general primitive-character
bound for *composite* modulus is therefore genuinely missing: it needs the
theory of primitive Dirichlet characters and the reduction of an imprimitive
Gauss sum to its primitive inductor — machinery not yet in Mathlib. So this
file converts the *prime part* of `gaussSumBound` from axiom to theorem and
pins the remaining work to the composite-primitive case.

## Results

- `conj_stdAddChar`         — conj of the standard additive character
- `conj_gaussSum`           — `conj (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹`
- `gaussSum_mul_conj`       — `τ(χ) · conj τ(χ) = p`
- `normSq_gaussSum`         — `normSq τ(χ) = p`
- `norm_gaussSum_eq_sqrt`   — **|τ(χ)| = √p** (the prime-modulus bound)
- `gaussSum_ne_zero`        — corollary: `τ(χ) ≠ 0`

Axioms: 0
Sorries: 0
-/
import Mathlib

open Finset Complex

namespace BoundedPrimeGapsOQ04OQ03

open scoped Real

noncomputable section

/-- Complex conjugation sends the standard additive character `e(a/N)` to its
inverse `e(-a/N)`: `conj (stdAddChar a) = stdAddChar⁻¹ a`.

The standard character takes values on the unit circle, so conjugation equals
inversion, and `stdAddChar⁻¹ a = stdAddChar (-a)`. -/
lemma conj_stdAddChar {N : ℕ} [NeZero N] (a : ZMod N) :
    (starRingEnd ℂ) (ZMod.stdAddChar a) = ZMod.stdAddChar⁻¹ a := by
  rw [ZMod.stdAddChar_apply, AddChar.inv_apply, ZMod.stdAddChar_apply,
      ← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv, Circle.coe_inv]

/-- Complex conjugation of a Gauss sum flips the character to its inverse:
`conj (gaussSum χ stdAddChar) = gaussSum χ⁻¹ stdAddChar⁻¹`.

Uses `conj (χ a) = χ⁻¹ a` (`MulChar.star_apply'`) termwise together with
`conj_stdAddChar`. -/
lemma conj_gaussSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) = gaussSum χ⁻¹ ZMod.stdAddChar⁻¹ := by
  rw [gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_mul, starRingEnd_apply, MulChar.star_apply', conj_stdAddChar]

variable (p : ℕ) [Fact p.Prime]

/-- For a nontrivial Dirichlet character mod a prime `p`, the Gauss sum
against the standard additive character satisfies `τ(χ) · conj τ(χ) = p`.

This is the product formula `gaussSum χ ψ · gaussSum χ⁻¹ ψ⁻¹ = #(ZMod p)`
(valid because `ZMod p` is a field) rewritten via `conj_gaussSum`. -/
theorem gaussSum_mul_conj (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    gaussSum χ ZMod.stdAddChar * (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) = (p : ℂ) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [conj_gaussSum,
      gaussSum_mul_gaussSum_eq_card hχ (ZMod.isPrimitive_stdAddChar p), ZMod.card]

/-- The squared norm of the Gauss sum equals `p`: `normSq τ(χ) = p`. -/
theorem normSq_gaussSum (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    Complex.normSq (gaussSum χ ZMod.stdAddChar) = (p : ℝ) := by
  have h : (Complex.normSq (gaussSum χ ZMod.stdAddChar) : ℂ) = (p : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
    exact gaussSum_mul_conj p χ hχ
  exact_mod_cast h

/-- **The Gauss sum bound, prime-modulus case.** For a prime `p` and any
nontrivial Dirichlet character `χ` mod `p`,

  ‖gaussSum χ stdAddChar‖ = √p .

This is `gaussSumBound` (Addition 1 of the BV prerequisite catalog,
`BoundedPrimeGapsOQ04OQ02`) restricted to prime modulus — proved here with
no axioms from Mathlib's `gaussSum_mul_gaussSum_eq_card`. -/
theorem norm_gaussSum_eq_sqrt (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt p := by
  rw [Complex.norm_def, normSq_gaussSum p χ hχ]

/-- Corollary: the Gauss sum of a nontrivial character mod a prime is nonzero.
(Its norm is `√p > 0`.) -/
theorem gaussSum_ne_zero (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    gaussSum χ ZMod.stdAddChar ≠ 0 := by
  have hp : (0 : ℝ) < Real.sqrt p := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    exact Real.sqrt_pos.mpr this
  intro h
  rw [← norm_gaussSum_eq_sqrt p χ hχ, h, norm_zero] at hp
  exact lt_irrefl 0 hp

end

end BoundedPrimeGapsOQ04OQ03
