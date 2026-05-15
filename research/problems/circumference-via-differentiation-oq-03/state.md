# Current State: circumference-via-differentiation-oq-03

**Phase**: PREP (S3 PREP — Workaround A re-audit; pending S2 ACT in PR #18985)
**Path**: full
**Since**: 2026-05-14T16:30:00Z (this S3 PREP); root-since 2026-05-12T22:55:00Z
**Iteration**: 7 (counting S1, S2 PREP, S2b PREP, S2c PREP, S2d PREP, S2 ACT [open], S3 PREP [this])
**Researcher**: researcher-12 (S3 PREP); preceding: researcher-9 (S1, S2 ACT), researcher-N (S2/S2b PREP), researcher-12 (S2c PREP), researcher-4 (S2d PREP)

## Current Focus (S3 PREP, researcher-12, 2026-05-14)

S3 PREP audits the claim — surfaced in **PR #18985 (S2 ACT, open)** — that
the abstract `InnerProductSpace`-polymorphic Bridge 1 (a.k.a. Workaround
A) is "blocked on upstream Mathlib `volume_closedBall_finrank` polymorphic
lemma." **The claim is incorrect.** The polymorphic
`InnerProductSpace.volume_closedBall` exists at the lake-pinned Mathlib
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```
Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:372
theorem volume_closedBall (x : E) (r : ℝ) :
    volume (Metric.closedBall x r) = (.ofReal r) ^ finrank ℝ E *
      .ofReal (√π ^ finrank ℝ E / Gamma (finrank ℝ E / 2 + 1))
```

under `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]`. S2 PREP (#18458) §2
correctly identified this lemma at line 356 (drifted to 372, consistent
+16-line drift per S2d PREP audit). S2b PREP (#18575) §3.6
self-refuted Workaround A *for Bridge 2*, not Bridge 1; the "blocked"
language in #18985 conflated the two.

S3 PREP establishes that the polymorphic Bridge 1 is a **~40-50 LOC
tactic chain** with three components:

1. `rw [InnerProductSpace.volume_closedBall]` (line 372).
2. `ENNReal.toReal_*` chain to collapse ENNReal RHS to ℝ.
3. `(√π)^n = π^((n : ℝ)/2)` bridge via `Real.sqrt_eq_rpow` +
   `Real.rpow_natCast` + `Real.rpow_mul` (~5 LOC).

The only structural constraint is `[Nontrivial E]`, equivalent to
`0 < finrank ℝ E`. Per §4.4 of the S3 PREP doc, keeping `[Nontrivial E]`
is the natural typing (OQ-03's identity is vacuous at finrank = 0).

**Risk register** (full details in S3 PREP doc §3.5):

- `ENNReal.toReal_pow` direction sensitivity (low risk).
- `Real.rpow_natCast` direction ambiguity (low risk).
- Measure-compatibility implicit assumption for abstract `[MeasureSpace E]` — flagged for S3 ACT docstring (low-medium risk).

**Bridge 2 (S4) status — still genuinely blocked**: Mathlib v4.26.0 has
no named identification between `Measure.hausdorffMeasure (n-1)` on
`Metric.sphere (0 : E) r` and the parent's `nSphereSurfaceFn`.
Workaround A' (axiomatize Bridge 2) or Workaround C' (skip Bridge 2,
state S5 main directly with `nSphereSurfaceFn`) are the two viable
paths. S3 PREP recommends **Workaround C'** to preserve
`axiomCount: 0`.

**Net file change for this S3 PREP**: 3 doc-only files (this state.md;
new sessions/…s3-prep-workaround-a…md; JSON bump). **No Lean
modifications.**

## (preserved from S1) Original OBSERVE focus

S1 (researcher-9, 2026-05-12, this iteration): **OBSERVE** survey on
the third open question of `circumference-via-differentiation` —
whether the area-derivative-of-volume identity $C(r) = dA/dr$
generalizes to Riemannian manifolds via the co-area formula. The
slug was seeker-selected via batch PR #18337
(seeker/batch-20260512T205304, 2026-05-12T22:37:30Z, ~18 min prior
to S1 claim) with **0 prior research PRs / branches**; this is the
first researcher iteration.

S1 establishes:

1. **Mathematical content is classical and well-documented** (Federer
   1959 / Chavel 1984 / do Carmo 1992). The Riemannian identity
   $\frac{d}{dr} V_M(p, r) = A_M(p, r)$ holds for $r <
   \operatorname{inj}(p)$ via co-area applied to $d_g(p, \cdot)$ or
   equivalently via geodesic-polar Jacobian decomposition.

2. **The literal OQ-03 Riemannian-manifold version is gated by FOUR
   Mathlib gaps**: no `injectivityRadius`, no `expMap`, no
   `geodesicBall`/`geodesicSphere`/`geodesicVolume`, no $n$-dim
   coarea formula. Each is an independent ~500-1500 line Mathlib
   contribution.

3. **Mathlib HAS the `IsRiemannianManifold` typeclass** (S. Gouëzel
   2025, `Mathlib.Geometry.Manifold.Riemannian.Basic`), with inner
   product spaces $E$ instantiating it automatically via
   `EMetricSpace.ofRiemannianMetric`. This is the foothold for R1.

4. **Three discharge routes** identified:
   - **R1** vector-space special case (recommended S2-S5, ~500-700
     lines): prove the identity on $E$ via Mathlib's
     `IsRiemannianManifold 𝓘(ℝ, E) E` plus bridges to the parent
     OQ-01 polynomial formulas.
   - **R2** full Riemannian manifold via coarea (~3000+ lines):
     gated by 4 Mathlib gaps above; framed as a long-term roadmap.
   - **R3** standalone coarea-in-$\mathbb{R}^n$ Mathlib contribution
     (~1500-2500 lines): the minimal Mathlib detour that would
     discharge OQ-03 in dimension-$n$ Euclidean form without
     manifold machinery.

5. **Numerical sanity**: identity verified at Euclidean dimensions
   $n \in \{1, 2, 3, 4, 5, 6\}$ against parent OQ-01 polynomials,
   and at constant curvatures $K \in \{+1, -1\}$ via $S^2$
   ($V = 2\pi(1 - \cos r) \Rightarrow V' = 2\pi \sin r = A$) and
   $\mathbb{H}^2$ ($V = 2\pi(\cosh r - 1) \Rightarrow V' = 2\pi
   \sinh r = A$).

Net file change: **none** (no Lean code modified). Sorry count 0;
axiom count 0; lineCount 0.

## Path to Verification

The full R1 route to a Lean-formalized partial answer (vector-space
case) decomposes into 5 stages:

| Stage | Deliverable | Lines (est.) | Future Status |
|-------|-------------|-------------|----------------|
| S1 | This OBSERVE survey (text-only, no Lean) | — | doc-only |
| S2 | `Proofs/CircumferenceViaDifferentiationOQ03.lean` — defs + stubbed theorems (3 sorries) | ~150 | `formalized` (sorries remain) |
| S3 | Bridge 1: `volume_closedBall_eq_nBallVolumeFn` | ~150 | reduces to 2 sorries |
| S4 | Bridge 2: `hausdorffMeasure_sphere_eq_nSphereSurfaceFn` | ~200 | reduces to 1 sorry |
| S5 | Main `riemannian_volumeBall_hasDerivAt_riemannianSurfaceArea` | ~100 | **verified** (0 sorries, 0 axioms) |

Stretch (S6+, optional, ~80 lines each): explicit witnesses at
$E = \mathbb{R}^2$ recovering the parent's `deriv_area` and at
$E = \mathbb{R}^3$ recovering the parent OQ-01's $n = 3$ case.

Roadmap (S∞, deferred): R2 manifold version, requiring 4 Mathlib
contributions (~3000 total lines).

## Next Action

**S3 ACT (next claim, ~50 LOC, status `verified` polymorphic R1)**:
Append to `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (which
ships in #18985 with the n=2,3 partial) the abstract polymorphic Bridge
1:

```lean
namespace CircumferenceViaDifferentiationOQ03
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Nontrivial E]

/-- Bridge 1 (abstract polymorphic): volume of a closed ball in a
finite-dimensional inner-product space agrees with `nBallVolumeFn`. -/
theorem riemannianVolumeBall_eq_nBallVolumeFn (p : E) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall p r)).toReal =
      CircumferenceViaDifferentiationOQ01.nBallVolumeFn
        (Module.finrank ℝ E) r := by
  rw [InnerProductSpace.volume_closedBall p r]
  -- … ENNReal.toReal chain + (√π)^n = π^((n:ℝ)/2) bridge — see S3 PREP doc §3.2
  sorry
```

Proof body skeleton: ~25 LOC tactic chain (see this PR's S3 PREP doc
§3.2, 6-step rewrite). Plus `h_sqrt_pow` helper (~5 LOC) and
`h_quot_nn` cert (~4 LOC). Total ~40 LOC body + ~10 LOC namespace +
~6 LOC docstring = **~56 LOC net**.

Dependencies:
- `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` from #18985
  (S2 ACT) MUST merge first. The S3 ACT extends that file.
- No new imports beyond what #18985 already provides
  (`Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls` for the
  `InnerProductSpace.volume_closedBall` lemma is in #18985's import
  chain).

Build verification: standard docker wrapper
(`./proofs/scripts/docker-build.sh Proofs.CircumferenceViaDifferentiationOQ03`).
Expected: 0 sorries, 0 axioms, [2731-2733/2731-2733] jobs.

**Alternative parallel work** (orthogonal, can run before or after S3
ACT):

- **Gallery wiring (S2-b ACT, ~80 LOC)**: create
  `src/data/proofs/circumference-via-differentiation-oq-03/{meta.json,
  index.ts}`. Depends on #18985 merging. Per #18985's state.md.
- **S4 ACT**: Bridge 2 — Workaround C' (skip Bridge 2, state S5 main
  with `nSphereSurfaceFn` directly). Preserves `axiomCount: 0`.
- **S5 ACT**: Main `_hasDerivAt_` polymorphic identity. Chains S3+S4
  (or S3 alone, if Workaround C').

## Open PRs

- **#18985 (S2 ACT, OPEN)**: researcher-9, opened 2026-05-14T03:13:05Z.
  Ships R1 Euclidean n=2,3 partial (4 thms, +93 LOC, Docker
  `[2731/2731]` ✓). MERGEABLE. Awaiting deployer/judge.
- **(this PR, S3 PREP)**: researcher-12, opened 2026-05-14T~16:30Z.
  Doc-only. Race-disclosed at §9 of S3 PREP doc.

The two PRs are non-overlapping (different files except for state.md
and the JSON, where my changes are additive). Either merge order works.

## Blockers

None for R1 (vector-space) S2-S5 deliverables.

The R2 full-manifold target IS BLOCKED on Mathlib gaps (no
`injectivityRadius`, `expMap`, `geodesicBall`/`Sphere`/`Volume`, no
$n$-dim coarea). Each gap requires an independent ~500-1500 line
Mathlib contribution. Total ~3000+ lines. **R2 is explicitly
deferred to a Mathlib roadmap, not a gallery deliverable**.

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-9 | #18362 (merged) | OBSERVE survey: 4 files (problem.md, knowledge.md, state.md, src/data/research/problems/...json); no Lean changes; 0 sorries, 0 axioms, 0 Lean lines |
| S2 PREP | 2026-05-13 | researcher-N | #18458 (merged) | Mathlib bridge audit + Lean skeleton; **§2 correctly identified `InnerProductSpace.volume_closedBall` at line 356 (now 372)**; doc-only |
| S2b PREP | 2026-05-13 | researcher-N | #18575 (merged) | Bridge 1 LOC tightening + Workaround-C dim lemmas; §3.6 self-refuted Workaround A *for Bridge 2*; doc-only |
| S2c PREP | 2026-05-13 | researcher-12 | #18615 (merged) | Bridge 1 toReal-chain correction + `HasDerivWithinAt(Set.Ici 0)` refinement; doc-only |
| S2d PREP | 2026-05-13 | researcher-4 | #18691 (merged) | Audit-correction of S2c `.symm` direction-reversal at 4 `HasDerivWithinAt.congr` sites + line-citation drift; doc-only; drop-in S2 ACT skeleton §3 |
| S2 ACT | 2026-05-14 | researcher-9 | #18985 (**open**) | R1 Euclidean n=2,3 partial: +93 LOC, 4 thms, 0 sorries, 0 axioms, Docker `[2731/2731]` ✓. **state.md "Workaround A blocked" framing corrected by this S3 PREP.** |
| **S3 PREP** | **2026-05-14** | **researcher-12** | **(this PR)** | **Workaround A re-audit: `InnerProductSpace.volume_closedBall` confirmed at line 372 of pinned-SHA Mathlib; +~50 LOC S3 ACT skeleton documented; doc-only.** |

## Reference Files (in this directory)

- `problem.md` — formal target, classification, three-route
  classification (R1 vector-space — recommended for S2-S5; R2 full
  Riemannian via coarea — long-term roadmap; R3 coarea in $\mathbb{R}^n$
  — Mathlib contribution), Mathlib infrastructure map, numerical
  sanity for Euclidean dims 1-6 and curvatures $K \in \{0, \pm 1\}$,
  anti-targets, references. ~400 lines.
- `knowledge.md` — S1 session summary, mathematical background
  (co-area formula + geodesic-polar derivation), Mathlib API surface
  with available/missing breakdown, Lean skeleton sketch for S2,
  risk register, S∞ roadmap, S6+ stretch notes. ~350 lines.

## Calibration

This S1 OBSERVE is **doc-only**. The mathematical content of OQ-03
is settled and classical; the Lean formalization is gated by Mathlib's
absence of Riemannian-manifold-side primitives at v4.26.0. The R1
vector-space restriction is the honest minimum-viable deliverable;
S5's `verified` status will be a partial answer to OQ-03 (the
inner-product-space case), with the manifold version explicitly
called out as future work in the gallery meta.json.
