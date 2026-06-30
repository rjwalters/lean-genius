/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Diagonal Jacobi sums are cyclotomic integers: `J(χ,χ) ∈ ℤ[ζ_n]`

For a finite field `F` and a multiplicative character `χ : F^× → R` of order dividing `n`
(i.e. `χ ^ n = 1`), the Jacobi sum

  `J(χ,χ) = ∑_{x ∈ F} χ(x) · χ(1 - x)`

lies in the subring `ℤ[μ] = Algebra.adjoin ℤ {μ}` generated over `ℤ` by a primitive `n`-th root
of unity `μ ∈ R`, rather than only in the ambient codomain `R`.

This is the **diagonal specialization** (`φ = χ`) of Mathlib's general two-character integrality
lemma
`jacobiSum_mem_algebraAdjoin_of_pow_eq_one`
(`Mathlib/NumberTheory/JacobiSum/Basic.lean`), which proves
`J(χ,φ) ∈ ℤ[μ]` whenever `χ ^ n = φ ^ n = 1`.

## Why the diagonal case

The diagonal Jacobi sum `J(χ,χ)` is the one that controls the higher power-reciprocity laws:
for the cubic and quartic laws one reads the reciprocity symbol off `J(χ,χ)` modulo a prime of
`ℤ[ζ_n]`, a step that only makes sense once `J(χ,χ)` is known to *live* in `ℤ[ζ_n]`. This file
records that membership as a standalone, directly citable statement, together with the
`orderOf χ = n` packaging that downstream developments usually have on hand.

## Main results

* `jacobiSum_self_mem_algebraAdjoin` — if `χ ^ n = 1` and `μ` is a primitive `n`-th root of
  unity, then `jacobiSum χ χ ∈ Algebra.adjoin ℤ {μ}`.
* `jacobiSum_self_mem_algebraAdjoin_of_orderOf` — the same conclusion phrased from the order
  hypothesis `orderOf χ = n`, via `pow_orderOf_eq_one`.
* `jacobiSum_isIntegral` / `jacobiSum_self_isIntegral` — the **algebraic-integer** consequence:
  `J(χ,φ)` (and the diagonal `J(χ,χ)`) is integral over `ℤ`. Membership in the subring `ℤ[μ]`
  is not literally `IsIntegral ℤ`; the upgrade uses that `ℤ[μ]` is a module-finite (hence
  integral) extension of `ℤ`, since the root of unity `μ` is integral over `ℤ`
  (`IsPrimitiveRoot.isIntegral`). This realizes the classical fact that Jacobi sums are
  algebraic integers — the precise sense in which `J(χ,χ) ∈ ℤ[ζ_n]` is a cyclotomic *integer*.

There are no new axioms or sorries: the proofs compose existing Mathlib lemmas.

## Honest scope

This is a routine specialization of an existing Mathlib lemma, not a new theorem. Its value is
as a small piece of reusable, precisely-stated infrastructure: the diagonal integrality fact in
the exact form the higher-reciprocity arguments invoke, with the order-of bridge supplied.
-/

open scoped BigOperators

variable {F R : Type*} [Fintype F] [Field F] [CommRing R] [IsDomain R]

/-- **Diagonal Jacobi-sum integrality.** If a multiplicative character `χ : MulChar F R` on a
finite field `F` satisfies `χ ^ n = 1`, and `μ ∈ R` is a primitive `n`-th root of unity, then the
diagonal Jacobi sum `J(χ,χ) = ∑ₓ χ(x)·χ(1-x)` lies in `ℤ[μ] = Algebra.adjoin ℤ {μ}`.

This is the `φ = χ` case of `jacobiSum_mem_algebraAdjoin_of_pow_eq_one`. -/
theorem jacobiSum_self_mem_algebraAdjoin {n : ℕ} [NeZero n] {χ : MulChar F R}
    (hχ : χ ^ n = 1) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    jacobiSum χ χ ∈ Algebra.adjoin ℤ {μ} :=
  jacobiSum_mem_algebraAdjoin_of_pow_eq_one hχ hχ hμ

/-- **Diagonal Jacobi-sum integrality, from the order of the character.** If `χ` has order exactly
`n` (so in particular `χ ^ n = 1` by `pow_orderOf_eq_one`), and `μ` is a primitive `n`-th root of
unity, then `J(χ,χ) ∈ ℤ[μ]`.

This is the form usually available downstream, where a character is presented together with its
order `n` (e.g. a character of order `3` for cubic reciprocity, `4` for quartic). -/
theorem jacobiSum_self_mem_algebraAdjoin_of_orderOf {n : ℕ} [NeZero n] {χ : MulChar F R}
    (hχ : orderOf χ = n) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    jacobiSum χ χ ∈ Algebra.adjoin ℤ {μ} :=
  jacobiSum_self_mem_algebraAdjoin (hχ ▸ pow_orderOf_eq_one χ) hμ

/-- **Jacobi sums are algebraic integers (general two-character form).** If `χ ^ n = φ ^ n = 1`
and `μ` is a primitive `n`-th root of unity in `R`, then `jacobiSum χ φ` is integral over `ℤ`.

Mathlib's membership lemma only places `J(χ,φ)` in the subring `ℤ[μ]`; this upgrades that to
genuine integrality over `ℤ`, using that `ℤ[μ] = Algebra.adjoin ℤ {μ}` is module-finite over `ℤ`
because the root of unity `μ` is integral over `ℤ` (`IsPrimitiveRoot.isIntegral`), so every
element of the adjoin is integral (`IsIntegral.of_mem_of_fg`). -/
theorem jacobiSum_isIntegral {n : ℕ} [NeZero n] {χ φ : MulChar F R}
    (hχ : χ ^ n = 1) (hφ : φ ^ n = 1) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    IsIntegral ℤ (jacobiSum χ φ) :=
  IsIntegral.of_mem_of_fg _
    (hμ.isIntegral (Nat.pos_of_ne_zero (NeZero.ne n))).fg_adjoin_singleton _
    (jacobiSum_mem_algebraAdjoin_of_pow_eq_one hχ hφ hμ)

/-- **The diagonal Jacobi sum is an algebraic integer.** `jacobiSum χ χ` is integral over `ℤ`
whenever `χ ^ n = 1` and `μ` is a primitive `n`-th root of unity. The `φ = χ` specialization of
`jacobiSum_isIntegral`; this is the precise sense in which `J(χ,χ) ∈ ℤ[ζ_n]` is a cyclotomic
*integer*, the object whose reduction modulo a prime of `ℤ[ζ_n]` defines the reciprocity symbol. -/
theorem jacobiSum_self_isIntegral {n : ℕ} [NeZero n] {χ : MulChar F R}
    (hχ : χ ^ n = 1) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    IsIntegral ℤ (jacobiSum χ χ) :=
  jacobiSum_isIntegral hχ hχ hμ

/-- The algebraic-integer conclusion phrased from the order hypothesis `orderOf χ = n`. -/
theorem jacobiSum_self_isIntegral_of_orderOf {n : ℕ} [NeZero n] {χ : MulChar F R}
    (hχ : orderOf χ = n) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    IsIntegral ℤ (jacobiSum χ χ) :=
  jacobiSum_self_isIntegral (hχ ▸ pow_orderOf_eq_one χ) hμ

#check @jacobiSum_self_mem_algebraAdjoin
#check @jacobiSum_self_mem_algebraAdjoin_of_orderOf
#check @jacobiSum_isIntegral
#check @jacobiSum_self_isIntegral
