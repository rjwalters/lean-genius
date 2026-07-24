# Research State: triangle-inequality-oq-04-oq-01

## Current State
**Phase**: COMPLETE (researcher-3, 2026-07-24, S3d ACT) — **`chartIntrinsicDist_triangle` PROVED**;
the chart-local Path-A program (S2a–S3d) is closed: ~500 LOC, 0 sorries, 0 axioms, verified with
the v4.31.0 toolchain against the pinned Mathlib olean cache. The 2026-06-13 verification-blackout
flag is cleared. **Slug-level status**: the original Riemannian target is now SUBSUMED upstream —
Mathlib v4.31 has `Mathlib.Geometry.Manifold.Riemannian.Basic` (`IsRiemannianManifold`,
`riemannianEDist` as infimum of path lengths, `EMetricSpace.ofRiemannianMetric` whose emetric
axioms include the triangle inequality) and `Riemannian/PathELength`. Pool marked `completed`;
a future slug could bridge this chart-local file to Mathlib's `riemannianEDist` if desired.
**Path**: A (chart-local Euclidean length) — COMPLETE
**Since**: 2026-07-24 (S3d)
**Iteration**: 8 (S1 OBSERVE, S2a ACT, S2b ACT, S3 PREP, S3a ACT, S3b ACT, S3c ACT, S3d ACT)

## Iteration 8 (researcher-3, 2026-07-24) — S3d ACT: chartIntrinsicDist_triangle SHIPPED (0 ax / 0 sorry)

**Outcome**: the chart-local triangle inequality
`chartIntrinsicDist p r ≤ chartIntrinsicDist p q + chartIntrinsicDist q r` is proved,
plus the supporting API: `chartIntrinsicDist_le_chartArcLength`, `chartIntrinsicDist_le_add`
(the concatenation bound), `chartIntrinsicDist_eq_zero_of_not_integrable`, `straightPath` +
`straightPath_integrable` (admissible witness), and integrability-transport iffs
`intervalIntegrable_trans_left_iff` / `_right_iff`.

**The S3 PREP "~10–20 LOC mirror" estimate was wrong** — two structural issues surfaced:

1. **Differentiability mismatch**: S3b/S3c lemmas required `f.extend` differentiable on `[0,1]`,
   but the infimum class of `chartIntrinsicDist` only carries speed-integrability. Fixed by
   strengthening the reparameterization adapters to UNCONDITIONAL form: new helpers
   `deriv_comp_mul_two` / `deriv_comp_mul_two_sub` prove `deriv (γ ∘ (·*2)) t = 2 • deriv γ (t*2)`
   for EVERY `γ` — chain rule when differentiable, and a bilateral junk-value argument otherwise
   (differentiability of the composite would transport back through the inverse affine map;
   both sides collapse to Mathlib's junk `0`). `chartArcLength_pathTrans` now needs NO
   differentiability hypotheses.
2. **ℝ-valued double-binder iInf collapse**: for inadmissible `γ` the inner
   `⨅ _ : (integrable…), …` is `Real.sInf ∅ = 0`, so ONE inadmissible path collapses
   `chartIntrinsicDist p q` to 0 (recorded as `chartIntrinsicDist_eq_zero_of_not_integrable`).
   The triangle inequality is still true, but the proof needs a case analysis: if a factor
   (say `f : p → q`) is inadmissible, then `f.trans (straightPath q r)` is an inadmissible
   `p → r` path (integrability transport, BACKWARDS direction of the iffs), so the left side
   collapses to 0 too. Hence the transports are proved as iffs. The assembly is elementary
   `ciInf_le` / `le_ciInf` over `innerLength` (private def naming the inner conditional iInf),
   with `straightPath` witnessing `Nonempty (Path _ _)`.

**Also degenerate but not load-bearing**: continuous nowhere-differentiable paths have junk
`deriv ≡ 0`, hence ARE admissible with `chartArcLength = 0` — so `chartIntrinsicDist` is 0
in any `E` admitting such paths (dim ≥ 1). The theorem proved here is the genuine gluing
argument, valid for any repaired path class; the definitional repair (e.g. a.e.-differentiable
paths with the derivative taken in a stronger sense, or ENNReal-valued length à la Mathlib's
new `Riemannian/PathELength`) is future work — but see the subsumption note above.

**Verification**: sibling-olean host check (researcher-1 cache, identical lake-manifest rev
`9a9483a929`), v4.31.0 toolchain binary; 0 errors, only the 3 pre-existing deprecation warnings.

**Landscape (v4.26 → v4.31)**: Mathlib now HAS the Riemannian stack this slug was created to
approximate: `IsRiemannianManifold I M`, `riemannianEDist`, `EMetricSpace.ofRiemannianMetric`
(triangle inequality built into the emetric axioms), `Riemannian/PathELength` (ENNReal path
length machinery). The original S1 finding "Mathlib has no RiemannianMetric typeclass" is stale.
**Last Updated**: 2026-06-12 (researcher-2, S3c ACT — shipped `chartArcLength_pathTrans` (concatenation additivity of `chartArcLength` along `Path.trans`) plus `Ioo`-interior helpers `eqOn_trans_first`/`eqOn_trans_second`; +96 LOC (206 → 302); 0 sorries / 0 axioms; build-verified 2590 Docker jobs clean. Discharges S3 PREP §8 sub-iter S3c. S3d `chartIntrinsicDist_triangle` main calc next.)

> **STATE-SYNC note (researcher-1, 2026-06-13)**: this header + the S3c ACT
> section below were back-filled. The S3c PR (researcher-2, 2026-06-12)
> shipped the source (`TriangleInequalityOQ04OQ01.lean` now 302 LOC,
> 0 sorries / 0 axioms, with `chartArcLength_pathTrans` @ line 250 and the
> two `eqOn_trans_*` helpers @ lines 212/227 on `origin/main`) and updated the
> JSON registry (iteration 7, S3c focus) but left this narrative at the S3b
> header. No build performed (verification blackout, Docker down); this edit
> only reconciles the tracker with the already-merged source.

## S3c ACT 2026-06-12 (researcher-2)

Discharges S3 PREP §8 sub-iter **S3c** (`chartArcLength_pathTrans`, LOW-MEDIUM
risk):

```lean
theorem chartArcLength_pathTrans {p q r : E} (f : Path p q) (g : Path q r)
    -- (differentiability + interval-integrability hypotheses) :
    chartArcLength (f.trans g).extend 0 1
      = chartArcLength f.extend 0 1 + chartArcLength g.extend 0 1
```

Concatenation additivity of `chartArcLength` along `Path.trans`. Proof: split
at `1/2` via `chartArcLength_trans`; on each half the concatenated speed agrees
a.e. with the reparametrised single-path speed — equal on the open interior via
two new helpers `eqOn_trans_first`/`eqOn_trans_second` (`Ioo`-versions of the
parent's `eqOn_first`/`eqOn_second`, sidestepping the `t = 1/2` case), lifted to
a `deriv` identity via `Filter.eventuallyEq_of_mem` + `EventuallyEq.deriv_eq`,
the lone boundary point Lebesgue-null (`MeasureTheory.ae_iff` +
`measure_mono_null` + `Real.volume_singleton`) — reducing each half to S3b's
adapters `chartArcLength_comp_mul_left`/`_shift`. +96 LOC (206 → 302);
0 sorries / 0 axioms; `omit [NormedSpace ℝ E]` on the two topology-only `eqOn`
helpers clears `unusedSectionVars`. Build-verified: 2590 Docker jobs clean.
**Next ACT (S3d)**: `chartIntrinsicDist_triangle` main calc (~10–20 LOC).

## S3b ACT 2026-06-05 (researcher-1)

Discharges S3 PREP §8 sub-iter **S3b** (reparametrisation adapters, MEDIUM risk):

```lean
private lemma chartArcLength_comp_mul_left {γ : ℝ → E}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ t) :
    chartArcLength (γ ∘ (· * 2)) 0 (1 / 2) = chartArcLength γ 0 1

private lemma chartArcLength_comp_mul_left_shift {γ : ℝ → E}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ t) :
    chartArcLength (γ ∘ (· * 2 - 1)) (1 / 2) 1 = chartArcLength γ 0 1
```

The S3 PREP §5 paste-ready skeleton had **two `sorry`s** on these reparam
adapters. This S3b **discharges both** via the refined 3-lemma chain catalogued
in S3b PREP §3 (PR #21305):

1. `deriv.scomp` (chain rule, `Mathlib/Analysis/Calculus/Deriv/Comp.lean:146`)
   gives `deriv (γ ∘ f) t = deriv f t • deriv γ (f t)`.
2. `norm_smul` + `Real.norm_ofNat` (Mathlib/Analysis/Normed/Group/Basic.lean:1097)
   extract the positive scalar `‖(2 : ℝ)‖ = 2`.
3. `smul_integral_comp_mul_right` (left half, `IntervalIntegral/Basic.lean:856`)
   or `smul_integral_comp_mul_sub` (right half, `Basic.lean:940`) collapses the
   substitution + scalar into a single bearer application.

Three new transitive imports needed:

- `Mathlib.Analysis.Calculus.Deriv.Mul` (for `hasDerivAt_mul_const`,
  `HasDerivAt.differentiableAt`/`.deriv`).
- `Mathlib.Analysis.Calculus.Deriv.Add` (for `HasDerivAt.sub_const`).
- `Mathlib.Analysis.Calculus.Deriv.Comp` (for `deriv.scomp`).

**Right-half affine shift** discharged via **Option α** from S3b PREP §4.2:
`smul_integral_comp_mul_sub (c d)` with `c := 2`, `d := 1` handles `c * x - d`
directly. Adapter introduces a small `mul_comm t 2` rewrite (via a second
`Set.EqOn` lemma) to convert chain-rule's `t * 2 - 1` into the bearer's
expected `2 * t - 1` form.

**Build verified**: `LEAN_BUILD_TIMEOUT=20m ./proofs/scripts/docker-build.sh Proofs.TriangleInequalityOQ04OQ01` → `Build completed successfully (2590 jobs).` (clean first-try after 1 syntactic fix: replaced `differentiableAt_id.mul_const 2` with `hasDerivAt_mul_const 2`-based construction; original would have required `FDeriv.Mul` transitively). Pin: Lean v4.26.0 + Mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Job count `2551 → 2590` (+39 jobs from 3 new Deriv.* imports).

**Sorries**: 0 (unchanged from S3a). **Axioms**: 0 (unchanged from S3a).

**Next ACT (S3c)**: assemble `chartArcLength_pathTrans` — additivity of
`chartArcLength` along `Path.trans` — by combining S2b's `chartArcLength_trans`
(interval-additivity at the midpoint `1/2`) with these two S3b adapters and
pointwise `Path.trans_extend` definition unfolding. Estimated 20–30 LOC,
LOW-MEDIUM risk per S3 PREP §6. After S3c ships, S3d (`chartIntrinsicDist_triangle`
main calc, ~10–20 LOC) closes the file.

See `sessions/2026-06-05-s3b-act-reparam-adapters.md` for the full deltas,
bearer audit, and pre-build-error fix log.

---

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

**S3c ACT** (next, LOW-MEDIUM risk — third of four S3 PREP §8 sub-iters):
assemble `chartArcLength_pathTrans` — additivity of `chartArcLength` along
`Path.trans` — by combining S2b's `chartArcLength_trans` (interval-additivity
at the midpoint `1/2`) with S3b's two reparametrisation adapters
(`chartArcLength_comp_mul_left` for the left half, `chartArcLength_comp_mul_left_shift`
for the right half) and pointwise `Path.trans_extend` definition unfolding.

The path-trans `extend` function unfolds to a piecewise definition matching
exactly the two adapter sites (`γ₁ ∘ (· * 2)` on `[0, 1/2]` and `γ₂ ∘ (· * 2 - 1)`
on `[1/2, 1]`). The adapters convert each chart-arc-length to the original
parameter; `chartArcLength_trans` glues at the midpoint.

Estimated 20–30 LOC.

After S3c ships, **S3d** (`chartIntrinsicDist_triangle` main calc, ~10–20 LOC)
closes the file: mirror parent `intrinsicDist_triangle`'s 2-step iInf-exchange
via `Real.iInf_add` / `Real.add_iInf` (R2 from S3 PREP §6 advises ad-hoc
derivation via `chartArcLength_nonneg` bound if those lemmas are absent for
`ℝ` — likely the case since the parent uses `ENNReal.iInf_add`).

**Total remaining S3 LOC**: ~20–30 (S3c) + ~10–20 (S3d) ≈ ~30–50 LOC.

**0 sorries / 0 axioms on completion** (per the original S3 PREP §3 estimate).

**Infrastructure gate**: ✅ Docker `29.5.2` server up at S3b claim time; disk 28
Gi avail. Docker R8 INFRASTRUCTURE blocker stayed resolved through S3b.

## Open PRs

- (this PR — S3 PREP) — `chartIntrinsicDist_triangle` design + paste-ready skeleton; doc-only.

## Iteration History (recent)

| Iter | Date       | Researcher     | PR          | Outcome                                                                                       |
|------|------------|----------------|-------------|-----------------------------------------------------------------------------------------------|
| S1   | 2026-05-12 | researcher-5   | #18333      | OBSERVE — Mathlib survey: no `RiemannianMetric`; 4 paths identified; Path A recommended for S2 |
| S2a  | 2026-05-14 | researcher-3   | #19100      | ACT — `chartArcLength` + 3 sanity lemmas; +60 LOC; Docker-verified (2551 jobs); 0 sorries, 0 axioms |
| S2b  | 2026-05-16 | researcher-1   | #19449      | ACT — `chartArcLength_trans` (additivity) via `intervalIntegral.integral_add_adjacent_intervals`; +18 LOC; Docker-verified (2551 jobs); 0 sorries, 0 axioms |
| S3   | 2026-05-16 | researcher-10  | #19561      | PREP — `chartIntrinsicDist_triangle` design (Option A: Path-mirror + reparam) + paste-ready skeleton (~120 LOC, 2 sorries on reparam adapters) + risk inventory (R1–R8) + ACT-readiness gate (6/8 GREEN, 1/8 AMBER, 1/8 RED Docker); doc-only |
| S3a  | 2026-05-30 | researcher-1   | #21188      | ACT — `chartIntrinsicDist` def + `chartIntrinsicDist_nonneg` discharged via nested `Real.iInf_nonneg`; +36 LOC (84 → 120); 0 new sorries / 0 new axioms; build-verified post-Docker-recovery (T+14d); discharges first of four S3 PREP §8 sub-iters |
| S3bPREP | 2026-05-30 | researcher-1 | #21305      | PREP — refined paste-ready recipe via `smul_integral_comp_mul_left` collapsing the S3 PREP 4-step chain to 3 bearers; 1 NEW catalogued bearer (`smul_integral_comp_mul_left` at IntervalIntegral/Basic.lean:866); doc-only |
| S3b  | 2026-06-05 | researcher-1   | #22474      | ACT — both reparam adapters discharged: `chartArcLength_comp_mul_left` + `chartArcLength_comp_mul_left_shift` via `deriv.scomp` + `norm_smul` + `smul_integral_comp_mul_right` / `smul_integral_comp_mul_sub` chain; +86 LOC (120 → 206); 0 new sorries / 0 new axioms; build-verified 2590 Docker jobs (+39 from 3 new Deriv.* imports); S3c (chartArcLength_pathTrans) next |
| S3c  | 2026-06-12 | researcher-2   | #22933      | ACT — `chartArcLength_pathTrans` (concatenation additivity along `Path.trans`) + `Ioo`-interior helpers `eqOn_trans_first`/`eqOn_trans_second`; split at 1/2 via `chartArcLength_trans`, a.e. speed agreement on each half reducing to S3b adapters, boundary point Lebesgue-null; +96 LOC (206 → 302); 0 sorries / 0 axioms; build-verified 2590 Docker jobs; S3d (`chartIntrinsicDist_triangle` main calc) next |
