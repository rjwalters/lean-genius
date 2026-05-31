# Current State: area-of-circle-oq-05-oq-04

**Phase**: RESEARCH (S6b ACT shipped — archimedean (C2) eigenfunction proven)
**Since**: 2026-05-31 (S6b ACT this PR ships parametric + (C2) + normSq Fourier-Gaussian; iter 11 → 12)
**Iteration**: 12 (S1 + S2a + S3 + S4a + S4b + S5 + S6a PREP + S6b PREP + S6c PREP + S6c PREP-2 + S6 ACT + **S6b ACT**)
**Last canonical sync**: 2026-05-31 (researcher-1, this PR — S6b ACT outcome + ledger refresh)

> _Phase note: Phase remains `RESEARCH` since the slug's remaining frontiers
> (Fourier-side `_shifted` + `_density_eigen` companions; the multi-week S6d
> Mathlib `Measure ℚ_p` milestone) are still open._

## Current Focus

**S6b ACT (this PR, 2026-05-31, researcher-1)** delivered the archimedean
analogue of (C2) via direct `fourier_gaussian_innerProductSpace`
specialization at `V := ℂ`. The Lean parent now contains 24 theorems +
2 private helpers across 771 LOC, all sorry-free and axiom-free. The
new theorems sit in a new Part 6:

- `complex_fourier_gaussian (b w)`: parametric form.
- `complex_fourier_gaussian_pi (w)`: the load-bearing **archimedean (C2)**
  — the standard complex Gaussian `exp(-π · ‖z‖²)` is a fixed point of `𝓕`.
- `complex_fourier_gaussian_normSq (b w)`: `Complex.normSq` companion.

The S11 PREP §4 skeleton flagged 2 R-class LOW sorries on side-corollaries
(`_normSq`, `_density_eigen`). The `_normSq` version came out **sorry-free**
via a `push_cast; ring` chain after `Complex.normSq_eq_norm_sq`. The
`_density_eigen` is deferred (Mathlib does not provide a `FourierModule`
instance for `(V → ℂ)`; needs hand-roll via `VectorFourier.fourierIntegral_const_smul`).

See `sessions/2026-05-31-s6b-act-complex-fourier-gaussian.md` for full
ACT detail (bearer recheck, departures from PREP, deferred next steps).

**S6 ACT (PR #19153, merged 2026-05-15T22:57Z, researcher-12)** delivered
the n-dimensional shifted complex Gaussian along Path B (per-axis Fubini,
S6a PREP recommendation), proven sorry-free and axiom-free.

The cumulative state is:

- **S6 ACT (last code, 2026-05-15)**: n-dim shifted complex Gaussian
  `∫_{Fin n → ℂ} exp(-(b·∑‖zᵢ-cᵢ‖²)) = (π/b)ⁿ` plus three corollaries
  (`normSq`, `b = 1` unit weight, `(b/π)ⁿ` density). Strict generalisation
  of both S4a (n-dim unshifted: `c = 0` reduction) and S5 (1-D shifted:
  `n = 1` reduction). Proven via heterogeneous Fubini
  (`integral_fintype_prod_volume_eq_prod`, chosen over the uniform
  `_eq_pow` because the per-axis factor depends on `i` through `cᵢ`)
  chained with `Real.exp_sum` factoring + per-axis S5 collapse. See
  `research/area-of-circle-oq-05-oq-04/s6-act-n-dim-shifted-gaussian.md`
  for the full ACT session report.
- **S6a PREP (2026-05-13, PR #18389, doc-only)**: pi-Haar one-shot vs
  per-axis Fubini route audit. Path B chosen. **Discharged by S6 ACT.**
- **S6b PREP (2026-05-13, PR #18422, doc-only)**: complex
  Fourier-eigenfunction via direct
  `fourier_gaussian_innerProductSpace` specialization at `V := ℂ`.
  **Pending ACT — sharpened by S11 PREP (this PR).**
- **S6c PREP (2026-05-13, PR #18488, doc-only)**: Schur orthogonality
  derivation route via parametric differentiation under the integral
  sign. **Superseded by S6c PREP-2.**
- **S6c PREP-2 (2026-05-13, PR #18584, doc-only)**: Mathlib
  `gaussianReal` / `IsGaussian` moment shortcut obsoletes
  `hasDerivAt_integral_of_dominated_loc` for the diagonal Schur case.
  **Pending ACT (orthogonal to S6b; deferred per §below).**
- **STATE-SYNC (2026-05-15, PR #19043, doc-only)**: canonical state.md
  consolidation. **Merged 30 min after S6 ACT but its content predates
  the ACT**; the post-ACT decomposition table and next-action wording
  in #19043's canonical state.md was already stale at merge time.
  This S11 PREP fixes that aging.
- **S11 PREP (this PR, doc-only)**: STATE-SYNC absorbing S6 ACT +
  sharpened S6b PREP-2 (bearer recheck, import-gap patch, concretized
  ~80-LOC paste-ready ACT skeleton). 3 files: this state.md rewrite,
  new sessions memo, research JSON refresh.

## Built (Lean, cumulative through S6 ACT)

In `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (658 lines, 21 theorems + 2
private helpers; S2a → S6 ACT):

- **S2a (b = π)**: `integral_pi_gaussian`, `complex_gaussian_integral`,
  `complex_gaussian_integral_norm`. Proven via
  `Complex.volume_preserving_equiv_real_prod` + `integral_prod_mul`
  + `scaled_gaussian`.
- **S3 (parametric b)**: `integral_b_gaussian`,
  `complex_gaussian_integral_scaled`,
  `complex_gaussian_integral_scaled_norm`,
  `complex_gaussian_integral_unit_norm` (b = 1, value π),
  `complex_gaussian_integral_normalised` (1/π density integrates to 1).
- **S4a (n-dim unshifted)**: `complex_gaussian_integral_scaled_pow`,
  `complex_gaussian_integral_scaled_pow_normSq`,
  `complex_gaussian_integral_pow_unit_norm`,
  `complex_gaussian_integral_pow_normalised`. Proven via
  `Real.exp_sum` reduction + `integral_fintype_prod_volume_eq_pow` +
  per-axis S3 factor.
- **S5 (1-D translation invariance + (c, b)-density)**:
  `complex_gaussian_integral_scaled_shifted_norm`,
  `complex_gaussian_integral_scaled_shifted`,
  `complex_gaussian_integral_unit_shifted_norm`,
  `complex_gaussian_density_shifted`. Proven via
  `MeasureTheory.integral_add_right_eq_self` (volume on ℂ is
  `IsAddHaarMeasure` ⇒ `IsAddRightInvariant`) chained with the
  unshifted parametric Gaussian.
- **S6 ACT (n-dim shifted)** *(NEW)*:
  `complex_gaussian_integral_scaled_pow_shifted_norm`,
  `complex_gaussian_integral_scaled_pow_shifted_normSq`,
  `complex_gaussian_integral_pow_unit_shifted_norm`,
  `complex_gaussian_density_pow_shifted`. Proven via heterogeneous
  Fubini (`integral_fintype_prod_volume_eq_prod`) + `Real.exp_sum`
  factoring + per-axis collapse to S5 shifted theorem.

Private helpers: `exp_factor`, `exp_factor_b` (S3 chain).

All proofs sorry-free and axiom-free; build verified via Docker wrapper
at S6 ACT close (2026-05-14 ~23:00 UTC, 3123/3123 jobs).

## Status

- Sorries: 0
- Axioms: 0
- Build: verified at S6b ACT close (2026-05-31 via Docker wrapper,
  `./proofs/scripts/docker-build.sh Proofs.AreaOfCircleOQ05OQ04`).
- Open Lean PR: **this PR (S6b ACT)** as of 2026-05-31T18:30Z UTC.
  No other open PRs for the slug (`gh pr list --state open --search
  "area-of-circle-oq-05-oq-04"` returned `[]` immediately before this PR).

## Path-to-completion (consolidated)

| Session | Phase | Deliverable | PR | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Markdown set + three-statement repair (C1/C2/C3 + bonus) | #17986 | merged |
| S2a | ACT-A | `complex_gaussian_integral` (b = π) | #18025 | merged |
| S3 | ACT-B | Parametric in `b > 0` + 3 corollaries | #18058 | merged |
| S4a | ACT | n-dim `∫_{ℂⁿ} exp(-b·∑‖zᵢ‖²) = (π/b)ⁿ` + 3 corollaries | #18221 | content merged via #18278; PR itself was OPEN/CONFLICTING (now apparently closed) |
| S4b | OBSERVE | p-adic Mathlib gap survey (doc-only) | #18269 | merged |
| S5 | ACT | 1-D translation invariance + `(c, b)`-density | #18278 | merged |
| S6a | PREP | n-dim shifted: pi-Haar vs Fubini route audit | #18389 | merged (discharged by S6 ACT) |
| S6b | PREP | Complex Fourier-eigenfunction via `fourier_gaussian_innerProductSpace` | #18422 | merged (sharpened by S11 PREP this PR) |
| S6c | PREP | Schur orthogonality via parametric differentiation | #18488 | merged (superseded by S6c PREP-2) |
| S6c PREP-2 | PREP | Moment-shortcut obsoletes `hasDerivAt_integral_of_dominated_loc` | #18584 | merged |
| **S6 ACT** | **ACT** | **n-dim shifted complex Gaussian + 3 corollaries (Path B per S6a)** | **#19153** | **merged 2026-05-15T22:57Z** |
| STATE-SYNC | DOC | Canonical state.md + JSON refresh after 10-session arc | #19043 | merged 2026-05-15T23:27Z (predates S6 ACT content) |
| **S11 PREP** | **PREP** | **S6b sharpened + STATE-SYNC absorbing S6 ACT (this PR)** | **(this)** | **unmerged** |
| (next) | ACT | S6b ACT: `complex_fourier_gaussian` family on `V := ℂ` | — | unclaimed |

## Next Action

**S6b ACT (next research claim)**: direct
`fourier_gaussian_innerProductSpace` specialization at `V := ℂ`, per the
sharpened paste-ready skeleton in
`sessions/2026-05-16-s11-prep-s6b-sharpened.md` §4. ~80 LOC. Adds 1 new
import (`Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`).

The skeleton fully discharges the two main theorems (`complex_fourier_gaussian`
parametric, `complex_fourier_gaussian_pi` the load-bearing archimedean (C2))
and the with-shift companion. It has **2 acknowledged R-class LOW sorries**
on side-corollaries (`_normSq` and `_density_eigen`), each ≤5 LOC discharge
with named-lemma reduction sketches.

**ACT-readiness gate: 7/8 GREEN substantive + 1/8 RED INFRA** (the RED is
host disk pressure precluding Docker build; not a math gate). If host disk
recovers before next claim, S6b ACT can run a full build verify. If disk
pressure persists, ship S6b ACT with `(build pending — disk-full)`
qualifier per `feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent`.

**Deferred (orthogonal, not blocking S6b)**:

- **S6c via PREP-2 (Schur orthogonality, diagonal case)**: ~40-60 LOC
  variance computation via `gaussianReal`/`IsGaussian` moment shortcut.
  Independent of S6b; both can ship in either order.
- **S6d (Mathlib milestone — `Measure ℚ_p` with `μ(ℤ_p) = 1`)**: multi-week
  upstream Mathlib PR. Tracked in S4b survey #18269. The standard
  `ψ_p : ℚ_p → ℂ` contribution is heavier still.

## Open Blockers

- None on the archimedean side. All required Mathlib infrastructure
  for S6b (and S6c, S6 family) is verified to be present at
  `lake-manifest` SHA `2df2f0150c…` v4.26.0 by the S6b/S6c PREPs and
  this S11 PREP's bearer recheck (§3 of the sessions memo).
- p-adic case (C1, C2, C3) blocks on two missing Mathlib pieces:
  standard additive character `ψ_p : ℚ_p → ℂ` and explicit Haar
  measure on `ℚ_p` with `μ(ℤ_p) = 1`. Neither lands in this slug
  directly — they are S6d upstream Mathlib milestones.
- **Host disk infra (INFRA-only, not math)**: `/System/Volumes/Data`
  at 100% used / 6.9 Gi avail; Docker unsafe per
  `feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent`.
  ACT cycle requires either disk recovery or `(build pending)` qualifier.

## Repository housekeeping (out of scope for this S11 PREP)

This slug's *deeper* session content lives in a **misplaced flat
directory** `research/area-of-circle-oq-05-oq-04/` (not the canonical
`research/problems/area-of-circle-oq-05-oq-04/`). The flat dir
contains (unchanged from STATE-SYNC #19043 ledger):

- `knowledge.md` (284 LOC) — accumulated S1 through S5 insights
- `state.md` (141 LOC) — S6 ACT closing snapshot
- `problem.md` (121 LOC) — formal statement (duplicate of canonical)
- `s4b-padic-survey.md` (233 LOC), `s6a-prep-pi-haar-vs-fubini.md`
  (236 LOC), `s6b-prep-complex-fourier-eigenfunction.md` (225 LOC),
  `s6c-prep-schur-orthogonality.md` (272 LOC),
  `s6c-prep-2-mathlib-moment-shortcut.md` (276 LOC),
  `s6-act-n-dim-shifted-gaussian.md` (236 LOC, S6 ACT session report)

Consolidation (move flat → canonical) is **mechanic-sweep territory**
per `feedback_researcher_canonical_vs_flat_research_problems_dir_divergence`.

The gallery entry `src/data/proofs/area-of-circle-oq-05-oq-04/`
**does not exist** (only sister slugs `…oq-01-oq-02-oq-02-oq-01` and
`…oq-05-oq-02` have entries). Gallery initialization is **mechanic /
gallery-init scope**, not researcher.

The previously-open conflicting #18221 (S4a ACT) appears closed between
the S6 ACT merge and this S11 PREP — verify status on next claim.

## Reference Files

**In canonical dir (`research/problems/area-of-circle-oq-05-oq-04/`)**:
- `state.md` — this file (rewritten by S11 PREP this PR)
- `sessions/2026-05-16-s11-prep-s6b-sharpened.md` — S11 PREP detail (this PR; ~350 LOC; primary reference for S6b ACT)

**In misplaced flat dir (`research/area-of-circle-oq-05-oq-04/`)**:
- `knowledge.md` — S1-S5 accumulated insights (284 LOC)
- `state.md` — S6 ACT closing snapshot (141 LOC, fresh; tracks Path B chain)
- `problem.md` — formal statement, three candidate corrections (C1/C2/C3)
- `s4b-padic-survey.md` — p-adic Mathlib gap survey
- `s6a-prep-pi-haar-vs-fubini.md` — Path A vs Path B route comparison (discharged by S6 ACT)
- `s6b-prep-complex-fourier-eigenfunction.md` — Direct `fourier_gaussian_innerProductSpace` specialization (sharpened by S11 PREP)
- `s6c-prep-schur-orthogonality.md` — Parametric-differentiation route (superseded by S6c PREP-2)
- `s6c-prep-2-mathlib-moment-shortcut.md` — Mathlib `gaussianReal` moment shortcut
- `s6-act-n-dim-shifted-gaussian.md` — S6 ACT session report (236 LOC)
