# Research State: triangle-inequality-oq-04-oq-01

## Current State
**Phase**: ACT (S3a ACT — `chartIntrinsicDist` def + `chartIntrinsicDist_nonneg` discharged; build-verified)
**Path**: A (chart-local Euclidean length)
**Since**: 2026-05-14 (researcher-3, S2a)
**Iteration**: 5 (S1 OBSERVE, S2a ACT, S2b ACT, S3 PREP, S3a ACT)
**Last Updated**: 2026-05-30 (researcher-1, S3a ACT — shipped `chartIntrinsicDist` definition + `chartIntrinsicDist_nonneg` (nested `Real.iInf_nonneg`); +36 LOC (84 → 120); 0 new sorries / 0 new axioms; build-verified post-Docker-recovery (T+14d from S3 PREP infrastructure RED). Discharges first of four S3 PREP §8 sub-iters (S3a definition + nonneg). S3b reparam adapters next.)

## S3a ACT 2026-05-30 (researcher-1)

Discharges S3 PREP §8 sub-iter **S3a** (definition + nonneg, LOW risk):

```lean
noncomputable def chartIntrinsicDist (p q : E) : ℝ :=
  ⨅ (γ : Path p q)
    (_ : IntervalIntegrable (fun t => ‖deriv γ.extend t‖) MeasureTheory.volume 0 1),
    chartArcLength γ.extend 0 1

theorem chartIntrinsicDist_nonneg (p q : E) : 0 ≤ chartIntrinsicDist p q := by
  unfold chartIntrinsicDist
  refine Real.iInf_nonneg (fun γ => ?_)
  refine Real.iInf_nonneg (fun _ => ?_)
  exact chartArcLength_nonneg γ.extend zero_le_one
```

The S3 PREP §5 paste-ready skeleton had `chartIntrinsicDist_nonneg` listed with a
`sorry`. This S3a **discharges that `sorry`** unconditionally via nested
`Real.iInf_nonneg` calls (Mathlib v4.26.0, `Mathlib/Data/Real/Archimedean.lean:257`).

Two new transitive imports:

- `Mathlib.Topology.Connected.PathConnected` (for `Path p q` and `Path.extend`,
  same module the parent `Proofs.TriangleInequalityOQ04` imports).
- `Mathlib.Data.Real.Archimedean` (for `Real.iInf_nonneg`, verified at pinned SHA
  via raw-content fetch — three other call sites in Mathlib v4.26.0).

**Infrastructure status** (S3a claim time 2026-05-30): Docker `29.4.1` server up;
disk 63 Gi avail (T+14d from the S3 PREP RED INFRA snapshot of 6.9 Gi/100% +
daemon-hung-exit-124). R8 from the S3 PREP risk inventory is **resolved**.

**Bearer-pin drift**: ZERO drift since S2b ACT (PR #19449, 14 days ago) for the
three bearers actively used (`Real.iInf_nonneg`, `Path`/`Path.extend`,
`IntervalIntegrable`).

**Build verified**: `LEAN_BUILD_TIMEOUT=45m ./proofs/scripts/docker-build.sh Proofs.TriangleInequalityOQ04OQ01` → `Build completed successfully (2551 jobs).` (clean first-try; same job count as S2a/S2b — the two new imports absorbed by the existing transitive Mathlib closure). Pin: Lean v4.26.0 + Mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Sorries**: 0 (unchanged from S2b). **Axioms**: 0 (unchanged from S2b).

**Next ACT (S3b)**: discharge the two reparametrisation adapters
(`chartArcLength_comp_mul_left` and `chartArcLength_comp_mul_left_shift`) via the
3-lemma chain (`deriv.scomp` + `norm_smul` + `intervalIntegral.integral_comp_mul_left`).
Estimated 30–50 LOC each, MEDIUM risk per S3 PREP §6 (R1, R5, R6). This is the
load-bearing sub-iter — once shipped, S3c (`chartArcLength_pathTrans`) and S3d
(main calc) follow mechanically.

See `sessions/2026-05-30-s3a-act-chartintrinsicdist-def-and-nonneg.md` for the
full deltas, bearer audit, and risk audit for this iteration.

---

## S3 PREP 2026-05-16 (researcher-10)

Doc-only PREP packaging the **design space + paste-ready skeleton** for the named S2c → S3 ACT (`chartIntrinsicDist_triangle`). No Lean source touched.

**Key findings**:

1. **Parent's `intrinsicDist_triangle` proof structure** (lines 215–239 of `TriangleInequalityOQ04.lean`): 2-step calc using (I1) `pathLength_trans` for additivity + (I2) `ENNReal.iInf_add`/`ENNReal.add_iInf` for distributivity. The parent's `pathLength_trans` (lines 169–196) is itself 4 steps + 2 helper lemmas (`eqOn_first`, `eqOn_second`) + 2 image lemmas (`image_scale_half`, `image_shift_half`).
2. **Chart-local reparameterization has no direct analog** at v4.26.0: parent's `eVariationOn.comp_eq_of_monotoneOn` is a single lemma; the integral-form analog is a **3-lemma chain** — `deriv.scomp` (chain rule) + `norm_smul` (positive scalar) + `intervalIntegral.integral_comp_mul_left` (substitution). All 3 verified at pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
3. **Four design options surveyed** for `chartIntrinsicDist p q`:
   - **Option A (RECOMMENDED)**: `⨅ (γ : Path p q) (_ : IntervalIntegrable ...), chartArcLength γ.extend 0 1`. Mirrors parent. Reparam via 3-lemma chain. ~120 LOC.
   - Option B: Constructive concatenation (no iInf). Skirts the mathematical content but easy. ~40 LOC.
   - Option C: 6-fold-nested iInf over `(a, b, γ, hp, hq, hint)`. Painful unfolding. ~80 LOC.
   - Option D: iInf over `(γ : ℝ → E) (_ : ContDiff ℝ 1 γ) (hp : γ 0 = p) (hq : γ 1 = q)`. Needs C¹ extension machinery. ~150 LOC.
4. **Paste-ready skeleton** (~120 LOC, 1 def + 4 helpers + 1 main, 2 sorries on reparameterization adapters): provided in session memo §5.
5. **Risk inventory** (8 markers R1–R8): 3 LOW + 4 MEDIUM + 1 INFRASTRUCTURE (Docker hung). No HIGH.
6. **Bearer-pin drift recheck**: 4-spot-check at pinned SHA `2df2f0150c…` — ZERO drift since S2b ACT (PR #19449, ~5h13m ago).

**Infrastructure status** (2026-05-16T09:51Z): Docker daemon hung — `timeout 5 docker info --format '{{.ServerVersion}}'` → exit 124 (daemon unresponsive); `df -h /System/Volumes/Data` → 100% capacity, 6.9Gi avail. PREP is **doc-only** — does not require build.

**Next ACT (S3)**: paste the §5 skeleton into `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` and discharge the 2 reparameterization `sorry`s. Optionally decompose into 4 sub-iterations (S3a definition + nonneg, S3b reparam adapters, S3c `chartArcLength_pathTrans`, S3d main calc). Estimated 120 LOC total, 0 sorries, 0 axioms.

See `sessions/2026-05-16-s3-prep-chartintrinsicdist-design.md` for full design rationale, paste-ready code, API-bearer audit, and risk decomposition.

---

## S2b ACT 2026-05-16 (researcher-1)

Adds **additivity under interval concatenation** to `TriangleInequalityOQ04OQ01.lean`:

```lean
theorem chartArcLength_trans (γ : ℝ → E) {a b c : ℝ}
    (hab : IntervalIntegrable (fun t => ‖deriv γ t‖) MeasureTheory.volume a b)
    (hbc : IntervalIntegrable (fun t => ‖deriv γ t‖) MeasureTheory.volume b c) :
    chartArcLength γ a b + chartArcLength γ b c = chartArcLength γ a c := by
  simp only [chartArcLength]
  exact intervalIntegral.integral_add_adjacent_intervals hab hbc
```

Inserted at lines 65–83 (between `chartArcLength_nonneg` and `end TriangleInequalityOQ04OQ01`). File grew 66 → 84 LOC (+18 LOC: ~7 LOC body + 1 fact statement + ~10 LOC docstring).

Hypotheses are stated as `IntervalIntegrable` (not `a ≤ b ≤ c`) because `intervalIntegral.integral_add_adjacent_intervals` handles the orientation-aware case via Mathlib's signed-interval-integral convention — this matches the form needed for the upcoming S2c chart-local triangle inequality (`chartIntrinsicDist_triangle`).

**Build verified**: `LEAN_BUILD_TIMEOUT=15m ./proofs/scripts/docker-build.sh Proofs.TriangleInequalityOQ04OQ01` → `Build completed successfully (2551 jobs).` First-try clean at Lean 4.26.0 + Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. No new warnings.

**Sorries**: 0 (unchanged). **Axioms**: 0 (unchanged).

**Next ACT** (S2c): chart-local triangle inequality `chartIntrinsicDist_triangle` mirroring the parent `Proofs.TriangleInequalityOQ04.intrinsicDist_triangle` — uses `chartArcLength_trans` (this S2b) + `iInf` manipulation for the intrinsic-distance infimum.

---

## Current Focus

S2a ACT — chart-local Euclidean arc length: definition + sanity lemmas.

Delivered `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` (~60 LOC) with:

- `noncomputable def chartArcLength (γ : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖` — the chart-local Euclidean arc length of a curve
  landing in a normed space.
- `theorem chartArcLength_self (γ : ℝ → E) (a : ℝ) : chartArcLength γ a a = 0`
  via `intervalIntegral.integral_same`.
- `theorem chartArcLength_const (c : E) (a b : ℝ) :
  chartArcLength (fun _ => c) a b = 0` via `deriv_const'`.
- `theorem chartArcLength_nonneg (γ : ℝ → E) (hab : a ≤ b) :
  0 ≤ chartArcLength γ a b` via `intervalIntegral.integral_nonneg + norm_nonneg`.

**Build status**: verified at v4.26.0 (`docker-build.sh Proofs.TriangleInequalityOQ04OQ01`,
2551 jobs clean, no Mathlib v4.26.0 surface regressions in this scope).
**Sorries**: 0. **Axioms**: 0.

## Previous Focus

S1 OBSERVE (researcher-5, 2026-05-12) surveyed Mathlib v4.26.0 Riemannian
infrastructure, confirmed the structural blocker (no `RiemannianMetric`
typeclass), and identified four intermediate paths (A–D). The recommended S2
target was **Path A** (chart-local Euclidean length, ~150 LOC). S2a is the first
of three Path A sub-iterations.

## Active Approach

**Path A — chart-local Euclidean length**. We define the arc length of a curve
landing in `E` (a normed space) as the integral of `‖deriv γ t‖` over the
parameter interval. This is well-typed without any Riemannian metric: it relies
only on `Mathlib.Analysis.Calculus.Deriv.Basic` and
`Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`. When applied to
`φ ∘ γ̃` where `φ : U → E` is a chart map and `γ̃ : ℝ → U` is a path on a smooth
manifold, this measures the Euclidean length in the chart image.

The definition is **chart-local**: it depends on the chart `φ`. Different charts
give different arc lengths. The chart-local triangle inequality (S2c) will be a
foundation for an eventual chart-invariant Riemannian arc length, lifted via
partition-of-unity gluing once upstream Mathlib lands `RiemannianMetric`.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 1 (Path A, S2a)
- Approaches tried: 1 (Path A; only S2a delivered so far)

## Blockers

**Upstream Mathlib blocker** (full Riemannian formalization, deferred to
Path D): `RiemannianMetric` typeclass does not exist at v4.26.0. Not in scope
for Path A; S2a/b/c deliver a chart-local triangle inequality that does not
depend on the missing typeclass.

## Next Action

**S3b ACT** (next, MEDIUM risk — the load-bearing sub-iter from S3 PREP §8):
discharge the **two reparametrisation adapters** that the S3 PREP §5 skeleton
left as `sorry`s. Estimated 30–50 LOC each (60–100 LOC total).

1. `chartArcLength_comp_mul_left {γ : ℝ → E} (hγ : ∀ t ∈ Icc 0 1, DifferentiableAt ℝ γ t) : chartArcLength (γ ∘ (· * 2)) 0 (1/2) = chartArcLength γ 0 1`
   via the 3-lemma chain — `deriv.scomp` (chain rule) + `norm_smul` (positive
   scalar) + `intervalIntegral.integral_comp_mul_left` (substitution). All 3
   verified at pinned SHA per S3 PREP §4.
2. `chartArcLength_comp_mul_left_shift` — analogous for `γ ∘ (· * 2 - 1)` on
   `[1/2, 1]`, with an additional `integral_comp_add_right` for the affine
   shift.

After S3b ships, S3c (`chartArcLength_pathTrans`, ~20–30 LOC) and S3d
(`chartIntrinsicDist_triangle` main calc, ~10–20 LOC) follow mechanically.

**Total remaining S3 LOC**: ~60–100 (S3b) + ~20–30 (S3c) + ~10–20 (S3d) ≈ ~90–150 LOC.

**0 sorries / 0 axioms on completion** (per the original S3 PREP §3 estimate).

**Infrastructure gate**: ✅ Docker `29.4.1` server up at S3a claim time; disk 63
Gi avail. The S3 PREP-time R8 RED INFRA blocker (Docker hung exit 124, disk
6.9 Gi) is **resolved** as of 2026-05-30 (T+14d).

## Open PRs

- (this PR — S3 PREP) — `chartIntrinsicDist_triangle` design + paste-ready skeleton; doc-only.

## Iteration History (recent)

| Iter | Date       | Researcher     | PR          | Outcome                                                                                       |
|------|------------|----------------|-------------|-----------------------------------------------------------------------------------------------|
| S1   | 2026-05-12 | researcher-5   | #18333      | OBSERVE — Mathlib survey: no `RiemannianMetric`; 4 paths identified; Path A recommended for S2 |
| S2a  | 2026-05-14 | researcher-3   | #19100      | ACT — `chartArcLength` + 3 sanity lemmas; +60 LOC; Docker-verified (2551 jobs); 0 sorries, 0 axioms |
| S2b  | 2026-05-16 | researcher-1   | #19449      | ACT — `chartArcLength_trans` (additivity) via `intervalIntegral.integral_add_adjacent_intervals`; +18 LOC; Docker-verified (2551 jobs); 0 sorries, 0 axioms |
| S3   | 2026-05-16 | researcher-10  | #19561      | PREP — `chartIntrinsicDist_triangle` design (Option A: Path-mirror + reparam) + paste-ready skeleton (~120 LOC, 2 sorries on reparam adapters) + risk inventory (R1–R8) + ACT-readiness gate (6/8 GREEN, 1/8 AMBER, 1/8 RED Docker); doc-only |
| S3a  | 2026-05-30 | researcher-1   | (this PR)   | ACT — `chartIntrinsicDist` def + `chartIntrinsicDist_nonneg` discharged via nested `Real.iInf_nonneg`; +36 LOC (84 → 120); 0 new sorries / 0 new axioms; build-verified post-Docker-recovery (T+14d); discharges first of four S3 PREP §8 sub-iters |
