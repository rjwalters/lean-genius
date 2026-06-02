/-
  Brouwer Fixed Point OQ-01-OQ-02-OQ-03-OQ-02: S17 ACT-B-PRE (G11)

  Companion file installing the **G11 disk-zero substantive bridge** —
  the ULift-lifted form of `H_n_minus_1_ball_zero_substantive`, closing
  Gap-2 of S15 PREP (PR #21862) §4.

  Purpose: provide `H_n_minus_1_disk_zero_substantive`, the analogue of
  `H_n_minus_1_ball_zero_substantive` (main:310) re-targeted to the
  TopCat object `TopCat.disk.{0} n` (whose carrier is
  `ULift ↥(Metric.closedBall …)`). The existing ball-side substantive
  theorem ends on the raw subtype carrier
  `TopCat.of ↥(Metric.closedBall …)`; the S16 ACT-B integration needs
  the lifted form so it can chain via G8/G9 against
  `H_n_minus_1_sphere_nonzero_substantive` (main:375), which ends on
  `TopCat.diskBoundary n = TopCat.of (ULift ↥(Metric.sphere …))`.

  Single declaration in namespace `BrouwerOQ01OQ02`:

  * `H_n_minus_1_disk_zero_substantive` — `IsZero` on `TopCat.disk.{0} n`
    for `n ≥ 2`. Proof: build the homeomorphism
    `ULift ↥(closedBall) ≃ₜ ↥(closedBall)` from `Homeomorph.ulift`,
    promote to a TopCat iso via `TopCat.isoOfHomeo`, push through the
    singular-homology functor with `Functor.mapIso`, and transport
    `IsZero` via `Limits.IsZero.of_iso` from
    `H_n_minus_1_ball_zero_substantive n hn`.

  Companion-file (not inline) per the G6/G7/G8/G10 precedent:
  build-risk isolation + review parallelism. Build cost shares the
  G10 import closure (`Mathlib.Topology.Category.TopCat.ULift` adds
  `Homeomorph.ulift` + `TopCat.uliftFunctor`, both light).

  Net axiom delta: 0. Net theorem delta: +1.

  Bearer audit (Mathlib v4.26.0 / SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
  - `TopCat.isoOfHomeo` at `Mathlib/Topology/Category/TopCat/Basic.lean:174`
  - `Homeomorph.ulift` at `Mathlib/Topology/Homeomorph/Lemmas.lean:275`
  - `Limits.IsZero.of_iso` at `Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean:115`
    (signature: `IsZero Y → (X ≅ Y) → IsZero X` — note source/target).
-/

import Mathlib.Topology.Category.TopCat.ULift
import Proofs.BrouwerFixedPointOQ01OQ02

open CategoryTheory TopCat

namespace BrouwerOQ01OQ02

/-- **G11 disk-zero substantive bridge**: the ULift-lifted form of
    `H_n_minus_1_ball_zero_substantive`, on the disk carrier
    `TopCat.disk.{0} n`. For `n ≥ 2`, the `(n-1)`-th singular
    homology of the n-disk with `ℤ`-coefficients vanishes.

    Proof: instantiate `Homeomorph.ulift` at the ball-subtype carrier
    to get `ULift ↥(closedBall) ≃ₜ ↥(closedBall)`, promote to the
    TopCat iso `TopCat.disk.{0} n ≅ TopCat.of ↥(closedBall)` via
    `TopCat.isoOfHomeo`, push through `F :=
    (singularHomologyFunctor AddCommGrpCat.{0} (n - 1)).obj
    (AddCommGrpCat.of ℤ)` with `Functor.mapIso`, and transport
    `IsZero` via `Limits.IsZero.of_iso` from
    `H_n_minus_1_ball_zero_substantive n hn`.

    Closes Gap-2 of S15 PREP — together with G10's
    `Retraction.toTopCatHom` + `Retraction.section_identity`, the
    final S16 ACT-B integration is reduced to: 4 imports + n=1 branch
    decision + the §5 paste-ready body. -/
theorem H_n_minus_1_disk_zero_substantive (n : ℕ) (hn : 2 ≤ n) :
    Limits.IsZero
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0} (n - 1)).obj
          (AddCommGrpCat.of ℤ)).obj (TopCat.disk.{0} n)) := by
  have hball := H_n_minus_1_ball_zero_substantive n hn
  -- `Homeomorph.ulift : ULift X ≃ₜ X`. Instantiated at the ball-subtype
  -- carrier, this gives the homeomorphism between the disk's underlying
  -- type (a ULift) and the unlifted ball-subtype.
  have hHomeo :
      (TopCat.disk.{0} n : TopCat.{0}) ≃ₜ
        TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    Homeomorph.ulift
  -- Promote to a TopCat iso, push through the singular-homology functor,
  -- and transport `IsZero` from the ball-side substantive theorem.
  exact hball.of_iso
    (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0} (n - 1)).obj
        (AddCommGrpCat.of ℤ)).mapIso (TopCat.isoOfHomeo hHomeo))

end BrouwerOQ01OQ02
