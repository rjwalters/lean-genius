# S3a ACT — `chartIntrinsicDist` definition + `chartIntrinsicDist_nonneg`

**Date**: 2026-05-30
**Researcher**: researcher-1
**Phase**: ACT (S3a — first of four S3 sub-iterations from the S3 PREP §8 decomposition)
**Status**: source change, build-verified

## 0. TL;DR

Discharges sub-iter **S3a** from the S3 PREP §8 decomposition (researcher-10, PR #19561):
ships the **definition** of `chartIntrinsicDist` (Option A: Path-mirror with
`IntervalIntegrable` side-hypothesis) and the **non-negativity** lemma
`chartIntrinsicDist_nonneg`, discharged unconditionally via nested `Real.iInf_nonneg`.

- **+34 LOC** in `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` (84 → 118).
- **0 new sorries.** 0 new axioms.
- 1 new `def` (`chartIntrinsicDist`) + 1 new `theorem` (`chartIntrinsicDist_nonneg`).
- 2 new imports: `Mathlib.Topology.Connected.PathConnected` (for `Path`),
  `Mathlib.Data.Real.Archimedean` (for `Real.iInf_nonneg`).
- Build-verified via `./proofs/scripts/docker-build.sh Proofs.TriangleInequalityOQ04OQ01`.

The S3 PREP §5 skeleton listed `chartIntrinsicDist_nonneg` with a `sorry`. This S3a
**discharges that sorry** by a 4-line proof:

```lean
unfold chartIntrinsicDist
refine Real.iInf_nonneg (fun γ => ?_)
refine Real.iInf_nonneg (fun _ => ?_)
exact chartArcLength_nonneg γ.extend zero_le_one
```

## 1. Mathematical content

For `E` a normed space over `ℝ` and `p, q : E`, define

$$d_{\text{chart}}(p, q) := \inf \{ L(\gamma) : \gamma \in \mathrm{Path}(p, q),\ \|\gamma'(\cdot)\|_E \in \mathrm{IntervalIntegrable}([0,1]) \}$$

where $L(\gamma) = \int_0^1 \|\gamma.\mathrm{extend}'(t)\|_E \, dt = \texttt{chartArcLength}\ \gamma.\mathrm{extend}\ 0\ 1$.

The `IntervalIntegrable` filter is essential: Mathlib's Bochner integral returns `0`
on non-strongly-measurable integrands, so without the filter the infimum collapses
trivially to `0` via pathological reparametrisations. With the filter, every
contributing $L(\gamma)$ is the genuine chart-local Euclidean arc length, which is
non-negative by `chartArcLength_nonneg` (this S3a uses this as the load-bearing fact).

Non-negativity then holds unconditionally:

- If the outer `Path p q` set has **at least one** path satisfying the
  `IntervalIntegrable` filter: $d_{\text{chart}}$ is the infimum of a non-empty set
  of non-negative reals, so $\geq 0$.
- If **no** `Path p q` satisfies the filter (e.g. degenerate normed spaces or
  exotic `p ≠ q`): Mathlib's $\mathrm{sInf}$ of the empty set is `0` (by
  `Real.iInf_of_isEmpty` / `Real.sInf_def`), so $d_{\text{chart}} = 0 \geq 0$.

Both cases are handled uniformly by `Real.iInf_nonneg`, whose signature
$$(\forall i, 0 \leq f(i)) \to 0 \leq \bigsqcap_i f(i)$$
covers empty index types via the same convention.

## 2. Code diff

### 2.a. Imports (+2 lines)

```diff
 import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
 import Mathlib.Analysis.Calculus.Deriv.Basic
+import Mathlib.Topology.Connected.PathConnected
+import Mathlib.Data.Real.Archimedean
```

- `Mathlib.Topology.Connected.PathConnected` exposes `Path p q` and `Path.extend`
  (verified at pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, same module
  the parent `Proofs.TriangleInequalityOQ04` imports at line 47).
- `Mathlib.Data.Real.Archimedean` exposes `Real.iInf_nonneg` (located in the file
  at v4.26.0, line 257). Used at three other call sites in Mathlib v4.26.0:
  `Mathlib/Combinatorics/Schnirelmann.lean:61` (Schnirelmann density nonneg),
  `Mathlib/Topology/MetricSpace/Gluing.lean:104` (gluing predistance nonneg),
  `Mathlib/Data/ENNReal/Operations.lean` (auxiliary). The pattern at Schnirelmann
  matches our pattern (`Real.iInf_nonneg (fun _ => by positivity)`).

### 2.b. New definition (+12 lines including docstring)

```lean
/-- The chart-local intrinsic distance between two points p, q : E: the infimum
of chart-local arc lengths over all continuous paths γ : Path p q whose speed
‖deriv γ.extend (·)‖ is interval-integrable on [0, 1].
...
-/
noncomputable def chartIntrinsicDist (p q : E) : ℝ :=
  ⨅ (γ : Path p q)
    (_ : IntervalIntegrable (fun t => ‖deriv γ.extend t‖) MeasureTheory.volume 0 1),
    chartArcLength γ.extend 0 1
```

### 2.c. New theorem (+15 lines including docstring)

```lean
theorem chartIntrinsicDist_nonneg (p q : E) : 0 ≤ chartIntrinsicDist p q := by
  unfold chartIntrinsicDist
  refine Real.iInf_nonneg (fun γ => ?_)
  refine Real.iInf_nonneg (fun _ => ?_)
  exact chartArcLength_nonneg γ.extend zero_le_one
```

The proof is a verbatim copy of the S3 PREP §5 skeleton's `sorry` slot, with the
`sorry` discharged by two nested `Real.iInf_nonneg` calls and a closing
`chartArcLength_nonneg` (the S2a-shipped non-negativity lemma at `0 ≤ 1`).

## 3. Build verification

Run: `LEAN_BUILD_TIMEOUT=45m ./proofs/scripts/docker-build.sh Proofs.TriangleInequalityOQ04OQ01`.

Result: `Build completed successfully (2551 jobs).` — clean first-try, **same
job count** as S2a (PR #19100) and S2b (PR #19449). The new
`Mathlib.Topology.Connected.PathConnected` and `Mathlib.Data.Real.Archimedean`
imports were absorbed by the existing transitive closure (no incremental
Mathlib compile beyond the cached 7727 mathlib4 cache files). Final leaf step
`[2551/2551] Built Proofs.TriangleInequalityOQ04OQ01 (16s)`. No new warnings.

**Pin**: Lean `v4.26.0`, Mathlib commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged from S2b/S3 PREP).

## 4. Risk audit

The S3 PREP §6 risk inventory listed 8 markers (R1–R8). S3a touches:

| Marker | S3a outcome |
|--------|-------------|
| R1 (reparameterization chain rule + `IntervalIntegrable` plumbing, MEDIUM) | Not touched — deferred to S3b. |
| R2 (`Real.iInf_add` distributivity may not exist verbatim, LOW) | Not touched — only need `Real.iInf_nonneg` here, which does exist (verified §2.a). |
| R3 (nested iInf over `(γ) (h : Prop)` verbose plumbing, LOW) | Touched and clean — `Real.iInf_nonneg` lifts through both layers via two `refine` calls. |
| R4 (chartArcLength_pathTrans plumbing, MEDIUM) | Not touched — deferred to S3c. |
| R5 (`Path.extend` is C⁰ not C¹ at boundary, MEDIUM) | Not touched — nonneg argument is integral-free at the structural level (`chartArcLength_nonneg` already discharges the boundary). |
| R6 (`Path.differentiable_extend` not in Mathlib, MEDIUM) | Not touched — S3a does not need any differentiability of `γ.extend`. |
| R7 (`γ₁.trans γ₂` piecewise-smooth `deriv` jump at `t = 1/2`, LOW) | Not touched. |
| R8 (Docker daemon hung INFRASTRUCTURE) | **RESOLVED** at S3a claim time: `docker info --format '{{.ServerVersion}}'` → `29.4.1` (server up), `df -h /` → 63 Gi avail (down from the S3 PREP-time 6.9 Gi but well above the operational threshold). |

**Aggregate**: 1 R-marker actively engaged (R3) and discharged cleanly. R8
INFRASTRUCTURE resolved (Docker recovered between S3 PREP claim time
2026-05-16 and S3a claim time 2026-05-30, a 14-day gap).

## 5. Bearer-pin re-spot-check

Three bearers (all stable since S3 PREP recheck 2026-05-16T09:51Z):

| Bearer | Path | Status |
|--------|------|--------|
| `Real.iInf_nonneg` | `Mathlib/Data/Real/Archimedean.lean:257` | ✅ verified via raw GitHub fetch at SHA `2df2f0150c…` |
| `Path` + `Path.extend` | `Mathlib/Topology/Connected/PathConnected.lean` | ✅ verified — same module the parent imports |
| `IntervalIntegrable` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` | ✅ already imported (used in S2b) |

**Pin drift**: ZERO drift since S2b ACT (PR #19449, 14 days ago).

## 6. Next-iteration plan

The S3 PREP §8 decomposition's four sub-iters:

- **S3a (this PR)**: definition + nonneg. ✅ shipped.
- **S3b** (next, MEDIUM risk): the two reparameterization adapters
  `chartArcLength_comp_mul_left` and `chartArcLength_comp_mul_left_shift`.
  Discharges the **load-bearing** §5 skeleton sorries via the 3-lemma chain
  (`deriv.scomp` + `norm_smul` + `intervalIntegral.integral_comp_mul_left`).
  Estimated 30–50 LOC each (60–100 LOC total).
- **S3c** (MEDIUM risk): `chartArcLength_pathTrans` assembled from S2b's
  `chartArcLength_trans` + the two `chartEqOn_*` lemmas + the S3b adapters.
  Estimated 20–30 LOC.
- **S3d** (LOW risk): main `chartIntrinsicDist_triangle` calc, mirroring the
  parent's 2-step iInf-exchange structure. Estimated 10–20 LOC.

**Total remaining S3 LOC**: ~120 (matches the original S3 PREP §3 estimate).

After S3d, the file will have 0 sorries / 0 axioms (per the original S3 PREP gate).

## 7. Honest scope disclaimer (carried over from S1/S2/S3 PREP)

`chartIntrinsicDist` is **chart-local**: it depends on the embedding of the
manifold's chart codomain `E`, not on a Riemannian metric. Mathlib v4.26.0 has
no `RiemannianMetric` typeclass; this chart-local definition is a foundation
that will lift to a chart-invariant Riemannian arc length via partition-of-unity
gluing once upstream lands the typeclass. See the S1 OBSERVE memo
(`sessions/2026-05-12-s1-observe-riemannian-mathlib-survey.md`) for the four-path
roadmap and the S3 PREP memo
(`sessions/2026-05-16-s3-prep-chartintrinsicdist-design.md`) for the
chart-local design rationale.

## 8. Memory cross-references

- Predecessor S2b ACT: PR #19449 (researcher-1, 2026-05-16), shipped
  `chartArcLength_trans`.
- Predecessor S3 PREP: PR #19561 (researcher-10, 2026-05-16), shipped the
  paste-ready Lean skeleton + 4-option design space + 8-marker risk inventory.
- Parent slug `triangle-inequality-oq-04` (completed 2026-04-05): mirrors the
  proof structure adopted here (`Path`-indexed iInf + `intrinsicDist_triangle`).
- Sibling slugs `triangle-inequality-oq-01/02/03`: no overlap with this work
  (separate `.lean` files for separate triangle-inequality sub-questions).
