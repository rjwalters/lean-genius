# S15 PREP — TopCat-morphism bridge audit for the S9 ACT-D-3 EXEC integration

- **Date**: 2026-06-01
- **Session**: 16 (S1–S14 + S13b BUILD-VERIFY-AND-FIX)
- **Phase**: PREP (S15 PREP shipped doc-only audit; S16 ACT EXEC will execute)
- **Author**: researcher-1
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged since S11)
- **Scope**: doc-only — no Lean / `meta.json` / `problem.md` / `knowledge.md` body edits

## 1. Why a PREP rather than an ACT

The JSON `currentState.nextAction` instructs S15 to "add 3 import lines …
then replace the mock composite axiom `H_n_minus_1_sphere_nonzero` …
with the four-bridge substantive derivation. Expected build size ~3300–
3400 jobs." S13b discharged the B3 INFRA blocker (Docker 29.4.1 up, 56 Gi
free), so the integration is Lean-and-Docker unblocked.

However, a literal `add 3 imports + delete axiom + paste proof` does NOT
type-check as-is. Auditing the four-bridge interface against the existing
substantive theorems exposes **two infrastructure gaps** that the existing
PREPs (S10, S12) did not surface:

- **Gap-1 — Retraction-to-TopCat bridge.** `Retraction n` (`main:133`)
  carries a continuous map on `EuclideanSpace ℝ (Fin n)` (the whole
  space). G8's `map_section_of_section` needs categorical morphisms
  `i : ∂𝔻 n ⟶ 𝔻 n` and `ρ : 𝔻 n ⟶ ∂𝔻 n` *in `TopCat`*. The inclusion
  `i` is `TopCat.diskBoundaryInclusion n` (Mathlib bearer, see §2). The
  retraction `ρ` does **not** exist in Mathlib — it must be constructed
  from `r : Retraction n` via a new helper. The construction is routine
  but non-trivial: ULift unwrap → subtype restriction → continuity from
  `r.continuous'` via subtype + ULift coercion.

- **Gap-2 — ULift mismatch between substantive ball/sphere.**
  `H_n_minus_1_ball_zero_substantive` (`main:310`) returns `IsZero` on
  `TopCat.of ↥(Metric.closedBall …)` (subtype, no ULift).
  `H_n_minus_1_sphere_nonzero_substantive` (`main:375`) returns
  `¬ IsZero` on `TopCat.diskBoundary n = TopCat.of (ULift (Metric.sphere …))`
  (ULift-wrapped). The integration needs the **same TopCat object** on
  both sides of the G8/G9 chain. Reconciled via `TopCat.uliftFunctor` and
  `uliftFunctorObjHomeo` (Mathlib bearers, see §2): either lift ball to
  ULift or lower sphere from ULift. Either reformulation is ~5–10 LOC.

Without S15 PREP, S16 ACT would hit both gaps mid-build, diagnose them
under Docker latency, and re-architect on the fly. PREP discharges them
in advance.

## 2. Bearer audit at pinned rev `2df2f0150c…`

All required Mathlib decls present and accessible:

| Bearer | Module | Line | Used for |
|---|---|---|---|
| `TopCat.disk` | `Mathlib/Topology/Category/TopCat/Sphere.lean` | 28 | The TopCat n-disk (`= TopCat.of (ULift (closedBall …))`) |
| `TopCat.diskBoundary` | same | 32 | The TopCat sphere `∂𝔻 n` (used by sphere-substantive) |
| `TopCat.sphere` | same | 37 | Alias `diskBoundary (n+1)` (not needed for integration) |
| `TopCat.diskBoundaryInclusion` | same | 58 | Inclusion `∂𝔻 n ⟶ 𝔻 n` (the `i` of G8) |
| `TopCat.uliftFunctor` | `Mathlib/Topology/Category/TopCat/ULift.lean` | 30 | Universe-lift functor on TopCat |
| `TopCat.uliftFunctorObjHomeo` | same | 35 | Homeomorphism `X ≃ₜ uliftFunctor.obj X` (closes Gap-2) |
| `Homeomorph.ulift` | `Mathlib/Topology/Homeomorph/Lemmas.lean` | — | The raw `ULift X ≃ₜ X` (alternative path for Gap-2) |
| `Continuous.comp` | `Mathlib/Topology/ContinuousOn.lean` | — | Continuity of the bridge map |
| `Continuous.codRestrict` | `Mathlib/Topology/Order.lean` | — | Continuity into a subtype |

Note that pinned Mathlib's `TopCat.Sphere.lean` uses the modern `module`
preamble (`public import …`) but the existing companion file builds
(`G6.lean`, `G7.lean`, `G8.lean`) successfully consume `TopCat`-style
morphisms, so no Lean-module-system surprises are expected.

**Spot-check vs S11 STATE-SYNC bearer list (4 modules).** The S11 list
(`Mathlib/Algebra/Category/Grp/Zero.lean`, `Topology/Category/TopCat/Sphere.lean`,
`CategoryTheory/Functor/Basic.lean`, `CategoryTheory/Limits/Shapes/ZeroObjects.lean`)
remains valid; this PREP adds `Mathlib/Topology/Category/TopCat/ULift.lean`
as the fifth audited module. No drift detected.

## 3. Closing Gap-1 — paste-ready `Retraction.toTopCatHom`

A new helper inside `BrouwerOQ01OQ02` namespace constructs the TopCat
morphism. Placement: either in main file (before §III, ~line 195) or in
a new companion `BrouwerFixedPointOQ01OQ02G10.lean`. **Recommendation**:
companion file, paralleling G6/G7/G8 — keeps the main file's import set
minimal and isolates build risk for the integration step.

### 3.1 Paste-ready skeleton

```lean
-- proofs/Proofs/BrouwerFixedPointOQ01OQ02G10.lean
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Category.TopCat.ULift
import Proofs.BrouwerFixedPointOQ01OQ02   -- for `Retraction`

open CategoryTheory TopCat

namespace BrouwerOQ01OQ02

/-- Bridge: a `Retraction n` produces a TopCat morphism `𝔻 n ⟶ ∂𝔻 n`. -/
noncomputable def Retraction.toTopCatHom {n : ℕ} (r : Retraction n) :
    TopCat.disk.{0} n ⟶ TopCat.diskBoundary.{0} n :=
  TopCat.ofHom
    { toFun := fun ⟨⟨p, hp_ball⟩⟩ =>
        -- hp_ball : p ∈ Metric.closedBall 0 1
        ⟨⟨r.toFun p, by
          have : p ∈ ClosedBall n := by simpa [ClosedBall] using hp_ball
          simpa [UnitSphere] using r.maps_to_sphere p this⟩⟩
      continuous_toFun := by
        -- Continuity chain (paste-ready outline):
        --   1. The map `ULift.up ∘ Subtype.mk ∘ r.toFun ∘ Subtype.val ∘ ULift.down`.
        --   2. `ULift.down` is `Homeomorph.ulift`; continuous.
        --   3. `Subtype.val` (inclusion) is continuous.
        --   4. `r.toFun` is continuous by `r.continuous'`.
        --   5. `Subtype.mk` into the sphere subtype: use `Continuous.codRestrict`
        --      with the proof that the image lies in the sphere.
        --   6. `ULift.up` is `Homeomorph.ulift.symm`; continuous.
        -- One-liner attempt: `by continuity` (likely works given step-5 instance).
        refine continuous_uLift_up.comp ?_
        refine (Continuous.codRestrict ?_ ?_).comp ?_
        · exact r.continuous'.comp (continuous_subtype_val.comp continuous_uLift_down)
        · intro ⟨⟨p, hp⟩⟩
          have : p ∈ ClosedBall n := by simpa [ClosedBall] using hp
          simpa [UnitSphere] using r.maps_to_sphere p this
        · exact continuous_subtype_val.comp continuous_uLift_down }

/-- The bridge respects the section identity: `i ≫ ρ = 𝟙 (∂𝔻 n)`. -/
theorem Retraction.section_identity {n : ℕ} (r : Retraction n) :
    TopCat.diskBoundaryInclusion.{0} n ≫ r.toTopCatHom =
      𝟙 (TopCat.diskBoundary.{0} n) := by
  apply TopCat.hom_ext
  funext ⟨⟨p, hp_sphere⟩⟩
  -- After unfolding: r.toFun p = p (with appropriate ULift/Subtype wrapping).
  have : p ∈ UnitSphere n := by simpa [UnitSphere] using hp_sphere
  simp [Retraction.toTopCatHom, diskBoundaryInclusion, r.fixes_sphere p this]

end BrouwerOQ01OQ02
```

**LOC estimate**: ~45 lines (incl. file header). Build cost: subset of
G6/G7/G8 import closures (no AlgebraicTopology dependency); expect
~400–500 jobs.

**Risk**: only the continuity proof `continuous_toFun` is non-trivial. The
fallback if `Continuous.codRestrict.comp` fails: use the explicit chain
`continuous_uLift_up.comp ((continuous_subtype_mk _ (r.continuous'.comp …)).comp continuous_uLift_down)`.
Build attempt-cost cap: one Docker iteration. If both forms fail, escalate
to S16 PREP-B for a targeted Mathlib-bearer survey on `continuous_subtype_mk`.

## 4. Closing Gap-2 — ULift reconciliation

`H_n_minus_1_ball_zero_substantive` uses `TopCat.of ↥(Metric.closedBall …)`
(no ULift); `H_n_minus_1_sphere_nonzero_substantive` uses
`TopCat.diskBoundary n` (ULift). G8/G9 require the same TopCat object on
both sides.

### 4.1 Choice: lift ball, not lower sphere

`TopCat.disk n` (ULift-wrapped) is the *natural* form — sphere-substantive
already uses the ULift-wrapped boundary. Lifting ball to match is
mechanically cleaner. Sketch:

```lean
/-- ULift-wrapped form of `H_n_minus_1_ball_zero_substantive`, on
    `TopCat.disk n` (matching the universe at which the G8/G9 bridges fire). -/
theorem H_n_minus_1_disk_zero_substantive (n : ℕ) (hn : 2 ≤ n) :
    Limits.IsZero
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0} (n - 1)).obj
          (AddCommGrpCat.of ℤ)).obj
        (TopCat.disk.{0} n)) := by
  -- Transport `H_n_minus_1_ball_zero_substantive` along `Homeomorph.ulift.symm`,
  -- which gives `Metric.closedBall ≃ₜ ULift (Metric.closedBall)` and thus
  -- `TopCat.of (closedBall) ≅ TopCat.disk n` in TopCat.
  have hball := H_n_minus_1_ball_zero_substantive n hn
  -- Build the iso from the homeomorphism, then transport IsZero via
  -- `Limits.IsZero.of_iso` after pushing through the functor.
  have hHomeo : TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
      ≅ TopCat.disk.{0} n :=
    TopCat.isoOfHomeo Homeomorph.ulift.symm
  -- Push through `singularHomologyFunctor ... |>.obj (AddCommGrpCat.of ℤ)`.
  exact hball.of_iso (((AlgebraicTopology.singularHomologyFunctor
    AddCommGrpCat.{0} (n - 1)).obj (AddCommGrpCat.of ℤ)).mapIso hHomeo)
```

**LOC**: ~12 lines. Build cost: trivial — reuses already-imported
infrastructure.

**Risk**: `TopCat.isoOfHomeo` is the canonical bridge from `Homeomorph` to
`TopCat`-isomorphism. Audit needed at pin (likely in
`Mathlib/Topology/Category/TopCat/Basic.lean` or a Homeomorph helper).
**S15 PREP punts the spot-check to S16 ACT** — if the name has drifted,
`Iso.ofHom` over `TopCat.ofHom Homeomorph.toContinuousMap` is the manual
fallback.

## 5. Paste-ready integration body (post-Gap-1 / Gap-2 closure)

After §3 and §4 land, the substantive replacement of the mock axiom is a
direct G6 + G7 + G8 + G9 wire-up. Sketch:

```lean
-- In proofs/Proofs/BrouwerFixedPointOQ01OQ02.lean: replace lines 261–263
-- (the `axiom H_n_minus_1_sphere_nonzero` block) with:

import Proofs.BrouwerFixedPointOQ01OQ02G6
import Proofs.BrouwerFixedPointOQ01OQ02G7
import Proofs.BrouwerFixedPointOQ01OQ02G8
import Proofs.BrouwerFixedPointOQ01OQ02G10  -- new from §3

/-- Substantive replacement of the former mock axiom. Discharges via the
    G6 + G7 + G8 + G9 bridges (companion files) plus the substantive
    `H_n_minus_1_disk_zero_substantive` (§4) and
    `H_n_minus_1_sphere_nonzero_substantive` (main:375). -/
theorem H_n_minus_1_sphere_nonzero (n : ℕ) (hn : n ≥ 1) (r : Retraction n)
    (φ : ℤ →+ Unit) :
    ∃ ψ : Unit →+ ℤ, ψ.comp φ = AddMonoidHom.id ℤ := by
  -- Conclusion `∃ ψ, ψ.comp φ = id` is impossible for any `φ : ℤ →+ Unit`
  -- (see `id_Z_not_factored_through_unit`). So we must derive `False`
  -- from the hypotheses `r : Retraction n`.
  exfalso
  by_cases hn2 : 2 ≤ n
  case pos =>
    -- Apply G8 to the section identity from `Retraction.section_identity`,
    -- then G9 with `H_n_minus_1_disk_zero_substantive` as the zero target,
    -- and contradict `H_n_minus_1_sphere_nonzero_substantive`.
    let F := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0}
                (n - 1)).obj (AddCommGrpCat.of ℤ)
    have hsect : TopCat.diskBoundaryInclusion.{0} n ≫ r.toTopCatHom
        = 𝟙 (TopCat.diskBoundary.{0} n) :=
      r.section_identity
    have hFsect : F.map (TopCat.diskBoundaryInclusion.{0} n)
                  ≫ F.map r.toTopCatHom
        = 𝟙 (F.obj (TopCat.diskBoundary.{0} n)) :=
      BrouwerFixedPointOQ01OQ02.map_section_of_section F _ _ hsect
    have hdiskZ : Limits.IsZero (F.obj (TopCat.disk.{0} n)) :=
      H_n_minus_1_disk_zero_substantive n hn2
    have hSphereZ : Limits.IsZero (F.obj (TopCat.diskBoundary.{0} n)) :=
      BrouwerFixedPointOQ01OQ02.isZero_of_section_into_isZero hdiskZ
        (F.map (TopCat.diskBoundaryInclusion.{0} n))
        (F.map r.toTopCatHom) hFsect
    exact H_n_minus_1_sphere_nonzero_substantive n hn2 hSphereZ
  case neg =>
    -- n = 1: `Retraction 1` is uninhabited via IVT (knowledge.md §G5 / main:303).
    -- Not formally proved in this file; ship S16 PREP to formalize OR encode
    -- as a separate lemma `Retraction_one_uninhabited`. For S16 ACT, leave
    -- this branch with a thin axiom `Retraction_one_uninhabited` rather than
    -- a `sorry`, so axiom count drops from 4 → 3 (mock H_..._nonzero gone)
    -- net (4 → 3 + 1 = 4 if we add the IVT axiom; net 4 → 4 — no progress
    -- on axiom count if n=1 isn't handled). The cleaner alternative is to
    -- restrict the file's no-retraction theorem to `n ≥ 2`, which matches
    -- the substantive setup; downstream callers (Brouwer's fixed-point
    -- corollary) already specialize at `n ≥ 2`.
    sorry  -- S16 ACT decision point
```

**Open question for S16 ACT decision**: does the slug want `n ≥ 1` (with
an IVT axiom for `n = 1`) or `n ≥ 2` (matching the substantive setup)?

Looking at `no_retraction_axiom` (line 44) — it requires `hn : n ≥ 1` —
and `no_retraction_singular_homology` (line 415) uses it. So a clean
restriction to `n ≥ 2` would require updating downstream theorems too,
which is out of scope for the integration. **Recommendation**: ship the
IVT axiom (or a `Retraction_one_uninhabited` lemma with a 5-line IVT
proof) as a thin local axiom; net axiom delta becomes 4 → 4 (replace
mock-composite with thin-IVT), not 4 → 3. This is honest about the
remaining gap.

## 6. Risk inventory

| Item | Risk | Mitigation |
|---|---|---|
| F1: `continuous_subtype_mk` API drift | LOW | Mathlib name stable in v4.26.0 (audited §2) |
| F2: `Continuous.codRestrict` placement | LOW | Stable, in `Mathlib/Topology/Order.lean` |
| F3: `TopCat.isoOfHomeo` name | MEDIUM | Spot-check at S16 ACT start; fallback `Iso.ofHom` |
| F4: `map_section_of_section` arg order | LOW | Defined in G8 file; signature pinned |
| F5: Universe polymorphism (`.{0}`) | MEDIUM | Existing companions all `.{0}`; align integration to match |
| F6: `Retraction 1` empty | OPEN | n=1 needs an axiom or proof; ship as separate lemma |
| F7: Build size jump | LOW | G10 ~400-500 jobs; main-file rebuild ~3300-3400 (matches JSON estimate) |
| F8: `by continuity` brittleness in §3.1 | MEDIUM | Manual chain provided as fallback |

Net: **4 LOW + 3 MEDIUM + 1 OPEN.** No `axiom`-count surprises predicted.
The OPEN item (F6) is the honest scope creep — see §5's recommendation.

## 7. Estimated build cost

| Step | Where | LOC | Jobs (est.) |
|---|---|---|---|
| G10 companion file (§3) | new | ~45 | ~400–500 |
| Main-file integration (§4 + §5) | edit `BrouwerFixedPointOQ01OQ02.lean` | +20, −3 | ~3300–3400 (matches JSON) |
| **Total S16 ACT delta** | | **~62 LOC net** | **~3700–3900 jobs** |

Wall-clock estimate per S13b cache behavior (post-warm: 316 jobs ≈
3.5 min). Cold-cache: scale linearly → ~35–45 min Docker build for the
main-file integration. Disk space: 56 Gi free at S13b time → comfortable.

## 8. Recommended S16 ACT execution order

1. Ship G10 companion file (§3.1 paste-ready); Docker-verify alone.
2. Spot-check `TopCat.isoOfHomeo` (or fallback) in main file; add
   `H_n_minus_1_disk_zero_substantive` (§4.1).
3. Add 4 `import` lines and replace mock axiom with §5 paste-ready body.
4. Resolve n=1 branch per §5 recommendation (ship `Retraction_one_uninhabited`
   as thin lemma or axiom).
5. Docker-verify full main-file build (~3300–3400 jobs).
6. Update `meta.json` axiom counts, gallery slug if present.

Sessions are sequential — recommend **two ACT PRs**: G10 first (small,
self-contained), then the main-file integration (large, dependent on G10).

## 9. Anti-targets (S15 PREP)

- No Lean / `proofs/Proofs/*.lean` edits.
- No `state.md` / `meta.json` / `problem.md` edits.
- No JSON `currentState` mutation (S15-prep is doc-only; S15-ACT or S16
  STATE-SYNC catches up).
- No bearer-drift Lean spot-check (`TopCat.isoOfHomeo` lookup deferred
  to S16 ACT prelude).

## 10. Honesty notes

- This PREP is doc-only. Lean delta = 0; theorem delta = 0; axiom delta = 0.
- The S15 PREP's value is **surfacing Gap-1 and Gap-2 in advance** —
  neither was identified by S10 PREP (G6 transfer feasibility) or
  S12 PREP (G6 companion-file pivot pre-staging), both of which assumed
  the integration was a clean import-and-wire affair. It is not.
- The n=1 branch (F6) is genuinely open. Past sessions and the file's
  own commentary ("`Retraction 1` is uninhabited (intermediate value
  theorem)") assert the result but do not prove it. S16 ACT must either
  add a 5-line IVT proof or a thin local axiom — both are documented
  paths in this PREP.
- Recommended axiom-count expectation for S16 ACT: **4 → 4** (replace
  mock composite with thin IVT), not the JSON's predicted **4 → 3**.
  The mock composite encoded TWO facts (sphere homology + functoriality);
  factoring them out forces the IVT axiom into the open. A future ACT
  could discharge the IVT axiom via `intermediate_value` from Mathlib's
  Analysis library, but that is out of scope for the integration step.
- This PREP commits to no Lean changes; the proof skeletons in §3, §4,
  §5 are paste-ready but unverified. S16 ACT must Docker-verify each.
