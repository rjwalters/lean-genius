/-
  Brouwer Fixed Point OQ-01-OQ-02-OQ-03-OQ-02: S16 ACT-A

  Companion file installing the **G10 retraction-to-TopCat bridge** —
  the infrastructure piece identified by S15 PREP (PR #21862) §3 as
  the first of two gaps blocking the S9 ACT-D-3 EXEC integration.

  Purpose: convert a `Retraction n` (custom structure with continuous
  map on `EuclideanSpace ℝ (Fin n)`) into a categorical morphism
  `𝔻 n ⟶ ∂𝔻 n` in `TopCat`, so that G8 (`map_section_of_section`)
  and G9 (`isZero_of_section_into_isZero`) can fire on the inclusion-
  retraction pair `(diskBoundaryInclusion n, r.toTopCatHom)`.

  Two declarations are exposed in namespace `BrouwerOQ01OQ02`:

  * `Retraction.toTopCatHom` — the TopCat morphism built from the
    underlying retraction function, with ULift wrap/unwrap, subtype
    restriction (via `Continuous.codRestrict`), and continuity
    transported through the chain
    `ULift.up ∘ codRestrict r.toFun (UnitSphere n) _ ∘ Subtype.val ∘ ULift.down`.

  * `Retraction.section_identity` — the section identity
    `diskBoundaryInclusion n ≫ r.toTopCatHom = 𝟙 (∂𝔻 n)`, the
    categorical witness that `r` retracts the inclusion. Follows
    directly from `r.fixes_sphere` (the structure field asserting
    pointwise fixity on the sphere).

  Companion-file (not inline) per §N5 Option A precedent (G6 / G7 / G8):
  build-risk isolation + review parallelism. Build cost is a subset of
  the main file's import closure (no `AlgebraicTopology` dependency);
  expected ~400-500 jobs per S15 PREP §7.

  Net axiom delta: 0. Net theorem delta: +1 (plus 1 definition).
-/

import Mathlib.Topology.Category.TopCat.Sphere
import Proofs.BrouwerFixedPointOQ01OQ02

open CategoryTheory TopCat

namespace BrouwerOQ01OQ02

/-- **G10 retraction-to-TopCat bridge**: a `Retraction n` produces a
    TopCat morphism `𝔻 n ⟶ ∂𝔻 n`. The underlying function unwraps
    the `ULift (Metric.closedBall …)` carrier of `𝔻 n`, applies the
    retraction's continuous function, and repacks the result into the
    `ULift (Metric.sphere …)` carrier of `∂𝔻 n` using
    `r.maps_to_sphere`. Continuity is built from `r.continuous'`
    via `Continuous.codRestrict` and the ULift homeomorphism. -/
noncomputable def Retraction.toTopCatHom {n : ℕ} (r : Retraction n) :
    TopCat.disk.{0} n ⟶ TopCat.diskBoundary.{0} n :=
  TopCat.ofHom
    { toFun := fun x =>
        ⟨⟨r.toFun x.down.val, by
          have hp : x.down.val ∈ ClosedBall n := by
            simp [ClosedBall, x.down.property]
          simpa [UnitSphere] using r.maps_to_sphere x.down.val hp⟩⟩
      continuous_toFun := by
        refine continuous_uliftUp.comp
          (Continuous.codRestrict ?_ ?_)
        · exact r.continuous'.comp
            (continuous_subtype_val.comp continuous_uliftDown)
        · intro x
          have hp : x.down.val ∈ ClosedBall n := by
            simp [ClosedBall, x.down.property]
          simpa [UnitSphere] using r.maps_to_sphere x.down.val hp }

/-- **G10 section identity**: the inclusion-retraction pair
    `(diskBoundaryInclusion n, r.toTopCatHom)` satisfies the section
    equation `i ≫ ρ = 𝟙 (∂𝔻 n)` in `TopCat`. Direct consequence of
    `r.fixes_sphere`: on the boundary sphere, the retraction is the
    identity. -/
theorem Retraction.section_identity {n : ℕ} (r : Retraction n) :
    TopCat.diskBoundaryInclusion.{0} n ≫ r.toTopCatHom =
      𝟙 (TopCat.diskBoundary.{0} n) := by
  ext ⟨⟨p, hp⟩⟩
  have hsphere : p ∈ UnitSphere n := by
    simpa [UnitSphere] using hp
  apply ULift.ext
  apply Subtype.ext
  exact r.fixes_sphere p hsphere

end BrouwerOQ01OQ02
