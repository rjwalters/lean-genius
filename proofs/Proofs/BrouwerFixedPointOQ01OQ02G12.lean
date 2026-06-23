/-
  Brouwer Fixed Point OQ-01-OQ-02-OQ-03-OQ-02: S18 ACT-B (G12)

  Companion file installing the **G12 sphere-nonzero substantive bridge
  for retractions at `n ≥ 2`** — the final categorical wire-up identified
  by S15 PREP §5 as the payload of the main-file integration.

  Purpose: produce the existence statement currently encoded by the mock
  axiom `H_n_minus_1_sphere_nonzero` (main:261), specialized to `n ≥ 2`,
  via a substantive derivation chaining G10 + G8 + G11 + the main file's
  `H_n_minus_1_sphere_nonzero_substantive`. The conclusion is reached by
  `exfalso` after deriving the substantive contradiction
  `IsZero (H_{n-1}(𝕊^{n-1}))` ⨯ `¬ IsZero (H_{n-1}(𝕊^{n-1}))`.

  Single declaration in namespace `BrouwerOQ01OQ02`:

  * `H_n_minus_1_sphere_nonzero_for_retraction` — `n ≥ 2` substantive form
    of the existence statement. Same signature as the mock axiom modulo
    the `n ≥ 2` hypothesis (axiom uses `n ≥ 1`). Proof: `exfalso` + the
    homological chain.

  Companion-file (not inline) per the G6/G7/G8/G10/G11 precedent:
  build-risk isolation + review parallelism. Main-file integration
  (replacing the mock axiom with this theorem + an `n = 1` branch) is
  deferred to S19 ACT-C.

  ## Derivation chain (S15 PREP §5)

  1. `r : Retraction n` carries the geometric retraction `B^n → S^{n-1}`.
  2. **G10** `Retraction.toTopCatHom` packages `r` as a TopCat morphism
     `ρ : 𝔻 n ⟶ ∂𝔻 n`.
  3. **G10** `Retraction.section_identity` provides the section equation
     `diskBoundaryInclusion n ≫ ρ = 𝟙 (∂𝔻 n)` in TopCat.
  4. **G8** `map_section_of_section` transports the section through the
     singular-homology functor `F := H_{n-1}(·; ℤ)`:
     `F.map (incl) ≫ F.map ρ = 𝟙 (F.obj ∂𝔻 n)`.
  5. **G11** `H_n_minus_1_disk_zero_substantive` provides
     `IsZero (F.obj 𝔻 n)` (the ULift-lifted form of the ball-zero
     substantive theorem).
  6. **G8** `isZero_of_section_into_isZero` combines (4) + (5) to derive
     `IsZero (F.obj ∂𝔻 n)`.
  7. The main file's `H_n_minus_1_sphere_nonzero_substantive` asserts
     `¬ IsZero (F.obj ∂𝔻 n)`, contradicting (6).
  8. From `False`, `False.elim` produces any `ψ : Unit →+ ℤ` to discharge
     the existential conclusion.

  Net axiom delta: 0. Net theorem delta: +1.

  ## What this does NOT replace

  This file does NOT remove the main file's `axiom H_n_minus_1_sphere_nonzero`
  (line 261). That replacement is the S19 ACT-C step: a single edit to the
  main file changing `axiom` → `theorem` with a body that wraps this G12
  result for `n ≥ 2` and ships a thin local lemma `Retraction_one_uninhabited`
  (IVT-based, knowledge.md §G5) for `n = 1`. The split into G12 (this PR) +
  S19 ACT-C (the main-file edit) isolates the substantive derivation from
  the main-file rebuild risk.

  ## Bearer audit (Mathlib v4.26.0 / SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

  All bearers are reused from the existing chain — no new Mathlib imports
  beyond what G10/G11 already pull in:

  - `Brouwer FixedPointOQ01OQ02.map_section_of_section` (G8, file:92)
  - `BrouwerFixedPointOQ01OQ02.isZero_of_section_into_isZero` (G8, file:115)
  - `BrouwerOQ01OQ02.Retraction.toTopCatHom` (G10, file:50)
  - `BrouwerOQ01OQ02.Retraction.section_identity` (G10, file:73)
  - `BrouwerOQ01OQ02.H_n_minus_1_disk_zero_substantive` (G11, file:67)
  - `BrouwerOQ01OQ02.H_n_minus_1_sphere_nonzero_substantive` (main, file:375)
-/

import Proofs.BrouwerFixedPointOQ01OQ02
import Proofs.BrouwerFixedPointOQ01OQ02G8
import Proofs.BrouwerFixedPointOQ01OQ02G10
import Proofs.BrouwerFixedPointOQ01OQ02G11

open CategoryTheory TopCat

namespace BrouwerOQ01OQ02

/-- **G12 sphere-nonzero substantive for retractions (`n ≥ 2`)**:
    the existence statement currently encoded by the mock axiom
    `H_n_minus_1_sphere_nonzero` (main:261), proved substantively for
    `n ≥ 2` via the G6/G7/G8/G10/G11 chain.

    Signature matches the mock axiom modulo `n ≥ 2` (mock uses `n ≥ 1`,
    leaving `n = 1` to a future `Retraction_one_uninhabited` lemma per
    S15 PREP §5 / knowledge.md §G5).

    The conclusion is reached by `exfalso`: the homological chain derives
    `IsZero (H_{n-1}(𝕊^{n-1}))` (from G11 + G8 + G10), which contradicts
    `H_n_minus_1_sphere_nonzero_substantive`. From `False`, any
    `ψ : Unit →+ ℤ` discharges the existential. -/
theorem H_n_minus_1_sphere_nonzero_for_retraction
    (n : ℕ) (hn : 2 ≤ n) (r : Retraction n) (φ : ℤ →+ Unit) :
    ∃ ψ : Unit →+ ℤ, ψ.comp φ = AddMonoidHom.id ℤ := by
  exfalso
  -- The singular-homology functor at degree `n - 1`, coefficients `ℤ`.
  set F :=
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0}
        (n - 1)).obj (AddCommGrpCat.of ℤ)) with hF
  -- (G10) Section equation in TopCat.
  have hsect :
      TopCat.diskBoundaryInclusion.{0} n ≫ r.toTopCatHom
        = 𝟙 (TopCat.diskBoundary.{0} n) :=
    r.section_identity
  -- (G8) Transport the section through F.
  have hFsect :
      F.map (TopCat.diskBoundaryInclusion.{0} n) ≫ F.map r.toTopCatHom
        = 𝟙 (F.obj (TopCat.diskBoundary.{0} n)) :=
    BrouwerFixedPointOQ01OQ02.map_section_of_section
      F (TopCat.diskBoundaryInclusion.{0} n) r.toTopCatHom hsect
  -- (G11) The disk has zero `H_{n-1}`.
  have hdiskZ : Limits.IsZero (F.obj (TopCat.disk.{0} n)) :=
    H_n_minus_1_disk_zero_substantive n hn
  -- (G8) The retract of a zero object is zero.
  have hSphereZ : Limits.IsZero (F.obj (TopCat.diskBoundary.{0} n)) :=
    BrouwerFixedPointOQ01OQ02.isZero_of_section_into_isZero
      hdiskZ
      (F.map (TopCat.diskBoundaryInclusion.{0} n))
      (F.map r.toTopCatHom)
      hFsect
  -- Contradict the substantive sphere-nonzero theorem.
  exact H_n_minus_1_sphere_nonzero_substantive n hn hSphereZ

end BrouwerOQ01OQ02
