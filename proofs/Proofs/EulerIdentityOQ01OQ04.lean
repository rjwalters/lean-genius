/-
# Euler Identity → `AddCircle (2 * π) ≃+ Additive Circle` (OQ-01-OQ-04)

## Open Question

> Construct a group isomorphism `ℝ / (2π · ℤ) ≅ S¹` induced by Euler's
> exponential map `t ↦ exp(i · t)`.

## Answer

`addCircleEquivAdditiveCircle` packages Mathlib's existing topological
bijection `AddCircle.homeomorphCircle' : AddCircle (2 * π) ≃ₜ Circle`
into a full **additive-group isomorphism**

  `AddCircle (2 * π) ≃+ Additive Circle`.

The bijection is reused verbatim from `homeomorphCircle'`; the additive
structure comes from `AddCircle.toCircle_add`, which says
`AddCircle.toCircle (x + y) = AddCircle.toCircle x * AddCircle.toCircle y`
— interpreted through `Additive`, this is exactly the homomorphism law.

This is the OQ-04 packaging that Mathlib v4.26.0 stops short of: the
underlying bijection (`homeomorphCircle'`) and the homomorphism law
(`toCircle_add`) are both present, but the combined `≃+` is not exposed
as a named definition anywhere in Mathlib.

## Foundation

Sibling file `Proofs/EulerIdentityOQ01OQ01OQ01.lean` (241 LOC, 0 axioms,
0 sorries) proves the underlying claims for the project's own
`circleMap : ℝ → ℂ` (`circleMap_add`, `norm_circleMap`,
`circleMap_eq_one_iff` saying kernel = `2π·ℤ`,
`circleMap_surjective_unit_circle`). That file documents `S¹ ≅ ℝ/2πℤ`
in its §8 summary but does not construct the actual `≃+`.

This file completes that summary at the Mathlib-`Circle` level.

## Status

**Iter 3 ACT-1 scaffold (researcher-1, 2026-06-03)**: ships the
isomorphism wrapper with three `sorry`s marking the bijection-inverse
lemma applications. The structure compiles against the Mathlib API
identified in the Iter 1 ORIENT/PREP session log
(`sessions/2026-06-01-iter1-orient-prep-mathlib-bearer-audit.md`).
Each `sorry` is a 1-3 line `simp` / `rfl` chain over named Mathlib
lemmas (`homeomorphCircle'.left_inv`, `homeomorphCircle'.right_inv`,
`AddCircle.toCircle_add` + `Additive.ofMul_mul`). Discharge target:
Iter 4 ACT-2 (next researcher) or Aristotle companion.

- 0 axioms
- 3 sorries (`left_inv`, `right_inv`, `map_add'`)
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Tactic

open Real

namespace EulerIdentityOQ01OQ04

/-! ## §1. The Isomorphism `AddCircle (2 * π) ≃+ Additive Circle` -/

/-- **OQ-04 main definition**: the additive-group isomorphism

  `AddCircle (2 * π) ≃+ Additive Circle`

induced by Euler's exponential map `t ↦ exp(i · t)`.

The forward direction is `AddCircle.toCircle`, the canonical quotient
map; the inverse is the symm of Mathlib's `homeomorphCircle'`. The
homomorphism law `map_add'` reduces to `AddCircle.toCircle_add` after
unfolding the `Additive` wrapper.

Mathlib v4.26.0 provides:
  * `AddCircle.homeomorphCircle' : AddCircle (2 * π) ≃ₜ Circle`
    — topological bijection (a `Homeomorph`, NOT a `≃+`);
  * `AddCircle.toCircle_add : toCircle (x + y) = toCircle x * toCircle y`
    — the homomorphism law on the underlying multiplicative `Circle`;
  * `AddCircle.toCircle_zero : toCircle 0 = 1`.

This definition combines them into the packaged `≃+`. -/
noncomputable def addCircleEquivAdditiveCircle :
    AddCircle (2 * π) ≃+ Additive Circle where
  toFun x := Additive.ofMul (AddCircle.toCircle x)
  invFun y := AddCircle.homeomorphCircle'.symm (Additive.toMul y)
  left_inv x := by
    -- Goal (after `show`):
    --   AddCircle.homeomorphCircle'.symm (AddCircle.toCircle x) = x
    -- Strategy (Iter 4): `AddCircle.homeomorphCircle'` is a `≃ₜ` whose
    -- `toFun` simp-normal-form is `AddCircle.toCircle` (verbatim per
    -- the @[simps] attribute at `Mathlib/Analysis/SpecialFunctions/
    -- Complex/Circle.lean:168`). So this is `homeomorphCircle'.left_inv`
    -- after a single `rfl`-style rewrite identifying `AddCircle.toCircle x`
    -- with `homeomorphCircle' x`.
    sorry
  right_inv y := by
    -- Goal (after `show`):
    --   Additive.ofMul (AddCircle.toCircle
    --     (AddCircle.homeomorphCircle'.symm y.toMul)) = y
    -- Strategy: apply `homeomorphCircle'.right_inv` (after identifying
    -- the forward map with `AddCircle.toCircle`), then collapse
    -- `Additive.ofMul ∘ Additive.toMul = id`.
    sorry
  map_add' x y := by
    -- Goal:
    --   Additive.ofMul (AddCircle.toCircle (x + y)) =
    --     Additive.ofMul (AddCircle.toCircle x) +
    --     Additive.ofMul (AddCircle.toCircle y)
    -- Strategy: `AddCircle.toCircle_add` upgrades `(x + y)` to
    -- `toCircle x * toCircle y`; `Additive.ofMul_mul` rewrites the
    -- multiplicative `*` on `Circle` to additive `+` on
    -- `Additive Circle`.
    sorry

/-! ## §2. API: extracting the forward and inverse maps -/

/-- The forward map is exactly `AddCircle.toCircle`. -/
@[simp] theorem addCircleEquivAdditiveCircle_apply (x : AddCircle (2 * π)) :
    (addCircleEquivAdditiveCircle x : Additive Circle) =
      Additive.ofMul (AddCircle.toCircle x) := rfl

/-- The inverse map is exactly `homeomorphCircle'.symm`. -/
@[simp] theorem addCircleEquivAdditiveCircle_symm_apply (y : Additive Circle) :
    addCircleEquivAdditiveCircle.symm y =
      AddCircle.homeomorphCircle'.symm (Additive.toMul y) := rfl

/-! ## §3. Summary

`addCircleEquivAdditiveCircle` exhibits the structural statement behind
Euler's identity: the circle group `S¹` (carried here by Mathlib's
`Circle`) is the quotient of the additive real line by its `2π · ℤ`
lattice. The map `t ↦ exp(i · t)` is the canonical Lie-group exponential
of `S¹`, and this isomorphism is its quotient-by-kernel packaging.

Sibling formalizations:

* `Proofs/EulerIdentity.lean` — `exp(i · π) + 1 = 0` (the point identity);
* `Proofs/EulerIdentityOQ01.lean` — Euler's formula via Taylor series;
* `Proofs/EulerIdentityOQ01OQ01.lean` — axiom-elimination of the above;
* `Proofs/EulerIdentityOQ01OQ01OQ01.lean` — Lie-group hom version on
  `Multiplicative ℝ →* ℂˣ` (axiom-free; kernel `= 2π · ℤ`); this file
  upgrades that to the named quotient isomorphism on `S¹` (`Circle`).
-/

#check @addCircleEquivAdditiveCircle

end EulerIdentityOQ01OQ04
