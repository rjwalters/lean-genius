/-
  Brouwer Fixed Point OQ-01-OQ-02-OQ-03-OQ-02: S8 ACT-D-2 EXEC

  Companion file installing the **G7 algebraic bridge**

      ¬ IsZero (X : AddCommGrpCat) → ∃ x : X, x ≠ 0

  per knowledge.md §N (S8 ACT-D-2 DESIGN, PR #18945).

  Purpose: bridge from the `¬ IsZero (...)` shape produced by
  `sphere_singularHomology_nonzero` (B2 surrogate axiom in the main file,
  S7 ACT-D-1) to the existential `∃ x : X, x ≠ 0` shape needed by the
  forthcoming S9 ACT-D-3 derivation that will replace the mock axiom
  `H_n_minus_1_sphere_nonzero` with a substantive derivation.

  Two theorems are exposed:

  * `AddCommGrpCat.not_isZero_iff_nontrivial` — the `iff` form, an
    idiomatic Mathlib hook combining the existing
    `AddCommGrpCat.isZero_iff_subsingleton`
    (`Mathlib/Algebra/Category/Grp/Zero.lean`) with the standard
    `not_subsingleton_iff_nontrivial`
    (`Mathlib/Logic/Nontrivial/Defs.lean`).

  * `AddCommGrpCat.exists_ne_zero_of_not_isZero` — the existential
    corollary, obtained from `Nontrivial X` via the standard
    `Nontrivial.exists_pair_ne` + `sub_ne_zero.mpr` chain. Universe-
    monomorphic at `Type 0` to match the existing call sites in
    `BrouwerFixedPointOQ01OQ02.lean` lines 287–292 (B1 surrogate) and
    351–356 (B2 surrogate), both of which instantiate
    `singularHomologyFunctor AddCommGrpCat.{0}` at universe `0`.

  Build risk: only `Mathlib.Algebra.Category.Grp.{Basic,Zero}`,
  `Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects`, and
  `Mathlib.Logic.Nontrivial.Basic` are imported — a strict subset of
  the main file's import list. No `Topology.*` / `AlgebraicTopology.*`
  dependencies. Build cost is dominated by `AddCommGrpCat`'s own
  dependency closure (which the main file already imports), so the
  companion-file build adds ≲ 1 s on top of the existing mathlib cache.

  Net axiom delta: 0. Net theorem delta: +2.

  Companion-file (not inline) per §N5 Option A: build-risk isolation +
  review parallelism. Mirrors `KonigsbergOQ01OQ02Recipe.lean` precedent.
-/

import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Logic.Nontrivial.Basic

open CategoryTheory

namespace AddCommGrpCat

/-- **G7 algebraic bridge, iff form**: for an additive commutative group
    `X` in the bundled category, `X` is not a zero object iff its carrier
    is `Nontrivial`.

    Proof: rewrite `IsZero X` to `Subsingleton X` via
    `AddCommGrpCat.isZero_iff_subsingleton`
    (`Mathlib/Algebra/Category/Grp/Zero.lean`, generated from
    `CommGrpCat.isZero_iff_subsingleton` by `@[to_additive]`), then
    apply `not_subsingleton_iff_nontrivial`
    (`Mathlib/Logic/Nontrivial/Defs.lean`).

    Universe-monomorphic at `Type 0` to match the call-site universe in
    `BrouwerFixedPointOQ01OQ02.lean`. -/
theorem not_isZero_iff_nontrivial (X : AddCommGrpCat.{0}) :
    ¬ Limits.IsZero X ↔ Nontrivial X := by
  rw [AddCommGrpCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]

/-- **G7 algebraic bridge, existential form**: for an additive
    commutative group `X` in the bundled category, if `X` is not a zero
    object then there exists an element `x : X` with `x ≠ 0`.

    This is the form consumed by the forthcoming S9 ACT-D-3 derivation:
    `sphere_singularHomology_nonzero` produces `¬ IsZero (H_{n-1}(𝕊^{n-1}))`,
    and this lemma converts that obstruction into an explicit non-zero
    element witness, which combined with the G6 Unit-bridge (sibling
    PR #18011 Part VI) yields the `∃ ψ, ψ ∘ φ = id` shape currently
    encoded by the mock axiom `H_n_minus_1_sphere_nonzero`.

    Proof: convert to `Nontrivial X` via `not_isZero_iff_nontrivial`,
    extract a distinct pair `a ≠ b` via `Nontrivial.exists_pair_ne`,
    and witness with `a - b ≠ 0` via `sub_ne_zero.mpr`. -/
theorem exists_ne_zero_of_not_isZero
    (X : AddCommGrpCat.{0}) (hX : ¬ Limits.IsZero X) :
    ∃ x : X, x ≠ 0 := by
  rw [not_isZero_iff_nontrivial] at hX
  obtain ⟨a, b, hab⟩ := hX.exists_pair_ne
  exact ⟨a - b, sub_ne_zero.mpr hab⟩

end AddCommGrpCat
