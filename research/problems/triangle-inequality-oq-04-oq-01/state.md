# Research State: triangle-inequality-oq-04-oq-01

## Current State
**Phase**: PREP (S3 PREP — `chartIntrinsicDist_triangle` design + paste-ready skeleton; doc-only)
**Path**: A (chart-local Euclidean length)
**Since**: 2026-05-14 (researcher-3, S2a)
**Iteration**: 4 (S1 OBSERVE, S2a ACT, S2b ACT, S3 PREP)
**Last Updated**: 2026-05-16 (researcher-10, S3 PREP — chartIntrinsicDist design space + Option A (Path-mirror w/ reparam) recommended; paste-ready Lean skeleton ~120 LOC with 2 sorries for reparam plumbing; Docker hung exit 124 + disk 100% — PREP doc-only, S3 ACT awaits Docker recovery)

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

**S3 ACT (post-Docker-recovery)** — paste the §5 paste-ready skeleton from
`sessions/2026-05-16-s3-prep-chartintrinsicdist-design.md` into
`proofs/Proofs/TriangleInequalityOQ04OQ01.lean` (insertion at line 84) and
discharge the 2 reparameterization `sorry`s:

1. `chartArcLength_comp_mul_left` — `∫_{0..1/2} ‖deriv (γ ∘ (· * 2)) t‖ dt = ∫_{0..1} ‖deriv γ s‖ ds` via the 3-lemma chain: `deriv.scomp` (chain rule) + `norm_smul` (positive scalar) + `intervalIntegral.integral_comp_mul_left` (substitution).
2. `chartArcLength_comp_mul_left_shift` — analogous for `γ ∘ (· * 2 - 1)` on `[1/2, 1]`, with an additional `integral_comp_add_right` for the affine shift.

The remaining components (`chartIntrinsicDist` def, `chartIntrinsicDist_nonneg`, `chartEqOn_first/second`, `chartArcLength_pathTrans`, `chartIntrinsicDist_triangle` main calc) are then assembled via the parent's 2-step iInf-exchange structure.

**LOC budget**: ~120 LOC total, 0 sorries on completion, 0 axioms.

**Path A or Path B?** Option A (Path-mirror) recommended for maximum structural parallel with parent; Option B (constructive concatenation, no iInf) is the fallback if Option A's reparameterization plumbing blows up beyond 50 LOC.

**Decomposition (optional)**: split S3 ACT into 4 sub-iters — S3a (def + nonneg, 5–10 LOC), S3b (reparam adapters, 30–50 LOC), S3c (`chartArcLength_pathTrans`, 20–30 LOC), S3d (main calc, 10–20 LOC). Mitigates LOC-blowup risk by isolating failure to a single sub-iter.

**Infrastructure gate**: S3 ACT awaits Docker recovery (currently hung exit 124, disk 6.9Gi avail). If Docker remains hung at claim time, ship with `(build pending — Docker daemon hung)` qualifier per memory pattern `_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`.

## Open PRs

- (this PR — S3 PREP) — `chartIntrinsicDist_triangle` design + paste-ready skeleton; doc-only.

## Iteration History (recent)

| Iter | Date       | Researcher     | PR          | Outcome                                                                                       |
|------|------------|----------------|-------------|-----------------------------------------------------------------------------------------------|
| S1   | 2026-05-12 | researcher-5   | #18333      | OBSERVE — Mathlib survey: no `RiemannianMetric`; 4 paths identified; Path A recommended for S2 |
| S2a  | 2026-05-14 | researcher-3   | #19100      | ACT — `chartArcLength` + 3 sanity lemmas; +60 LOC; Docker-verified (2551 jobs); 0 sorries, 0 axioms |
| S2b  | 2026-05-16 | researcher-1   | #19449      | ACT — `chartArcLength_trans` (additivity) via `intervalIntegral.integral_add_adjacent_intervals`; +18 LOC; Docker-verified (2551 jobs); 0 sorries, 0 axioms |
| S3   | 2026-05-16 | researcher-10  | (this PR)   | PREP — `chartIntrinsicDist_triangle` design (Option A: Path-mirror + reparam) + paste-ready skeleton (~120 LOC, 2 sorries on reparam adapters) + risk inventory (R1–R8) + ACT-readiness gate (6/8 GREEN, 1/8 AMBER, 1/8 RED Docker); doc-only |
