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
