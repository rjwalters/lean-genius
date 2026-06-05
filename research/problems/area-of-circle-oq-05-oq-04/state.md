# Current State: area-of-circle-oq-05-oq-04

**Phase**: RESEARCH (S6c ACT-1 — `integral_sq_exp_neg_sq` via `gaussianReal` variance shortcut shipped, 3208/3208 jobs)
**Since**: 2026-06-04 (S6c ACT-1 this PR; iter 14 → 15)
**Iteration**: 15 (S1 + S2a + S3 + S4a + S4b + S5 + S6a PREP + S6b PREP + S6c PREP + S6c PREP-2 + S6 ACT + S6b ACT + S6b ACT-2 + S6c PREP-3 + **S6c ACT-1**)
**Last canonical sync**: 2026-06-04 (researcher-3, this PR — S6c ACT-1 ships `integral_sq_exp_neg_sq` per PREP-3 §3 route 2)

> _Phase note: Phase remains `RESEARCH` since the slug's remaining frontiers
> (Schur orthogonality S6c, n-dim Fourier-Gaussian lift, the multi-week S6d
> Mathlib `Measure ℚ_p` milestone) are still open. The 1-dim ℂ Fourier-Gaussian
> Part 6+7 frontier is now closed: `_shifted` + `_density_eigen` shipped this PR._

## Current Focus

**S6b ACT-2 (this PR, 2026-05-31, researcher-1)** shipped the 2 deferred
S6b companions as a new Part 7 of `proofs/Proofs/AreaOfCircleOQ05OQ04.lean`,
both sorry-free and axiom-free:

- `complex_fourier_gaussian_shifted (b w x)`: modulation companion —
  a `2π i · ⟪x, z⟫` phase shift in the input becomes a `w ↦ x - w`
  shift of the Fourier-domain Gaussian peak. Direct
  `fourier_gaussian_innerProductSpace'` specialization at `V := ℂ`.
- `complex_fourier_gaussian_density_eigen (w)`: the normalised density
  `(1/π) · exp(-π · ‖z‖²)` is a Fourier eigenfunction with eigenvalue 1.
  Proof: pull `(1/π)` out via `integral_const_mul`, reduce to
  `complex_fourier_gaussian_pi`. Tactic gotcha discovered:
  `Circle.smul_def` rewrites `Circle • a → (↑Circle : ℂ) • a` (still SMul),
  must follow with `smul_eq_mul` before `ring`.

Cumulative Lean state: 854 LOC / 26 theorems + 2 private helpers / 0
sorries / 0 axioms. Docker-verified 3129/3129 jobs at v4.26.0.

See `sessions/2026-05-31-s6b-act-2-deferred-companions.md` for full ACT
detail (tactic-engineering notes, delta breakdown, next-step roster).

**S6b ACT (PR prior, 2026-05-31, researcher-1)** delivered the archimedean
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
- Build: verified at S6c ACT-1 close (2026-06-04 via Docker wrapper,
  `./proofs/scripts/docker-build.sh Proofs.AreaOfCircleOQ05OQ04`),
  **3208/3208 jobs at v4.26.0**.
- Cumulative: 921 LOC / 27 theorems + 2 private helpers / 0 sorries / 0 axioms.
- Open Lean PR: this S6c ACT-1 PR (researcher-3, 2026-06-04).

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
| S11 PREP | PREP | S6b sharpened + STATE-SYNC absorbing S6 ACT | #19594 | merged 2026-05-16T09:57Z |
| **S6b ACT** | **ACT** | **`complex_fourier_gaussian` family on V := ℂ (Part 6, +3 thm, +`_normSq` companion sorry-free)** | **#21575** | **merged 2026-05-31T18:34Z** |
| **S6b ACT-2** | **ACT** | **`complex_fourier_gaussian_shifted` + `_density_eigen` (Part 7, +2 thm, sorry-free)** | **#21779** | **merged 2026-06-01T03:52Z** |
| STATE-SYNC | DOC | Path-to-completion + Next Action refresh post S6b ACT-2 | #21977 | merged 2026-06-01T19:23Z |
| S6c PREP-3 | PREP | Bearer recheck @ `2df2f0150c` + paste-ready `gaussianReal`-variance route for `integral_sq_exp_neg_sq` (~20-25 LOC ACT-1 skeleton) | (merged) | merged |
| **S6c ACT-1** | **ACT** | **`integral_sq_exp_neg_sq` via `gaussianReal 0 (1/2)` variance shortcut (Part 8, +1 thm, 22 LOC proof, 3208/3208 jobs)** | **(this)** | **unmerged** |
| (next) | ACT-2 | `complex_gaussian_integral_norm_sq` + n-dim `schur_orthogonality_complex_gaussian_diag` (~40-55 LOC) | — | unclaimed |

## Next Action

S6c ACT-1 (this PR, researcher-3, 2026-06-04) ships the load-bearing 1-D
real second moment

    integral_sq_exp_neg_sq : ∫ x : ℝ, x^2 * exp(-x^2) = √π / 2

as a new Part 8 of `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (Diagonal Schur
prerequisite). Proof: 22 LOC body via the `gaussianReal 0 (1/2 : ℝ≥0)`
variance shortcut (PREP-3 §3 route 2) — variance equals `∫ x² · pdf` since
the mean is 0, and `(√π)⁻¹·exp(-x²)` is the pdf at v = 1/2. Sorry-free,
axiom-free, Docker-verified 3208/3208 jobs at v4.26.0.

See `sessions/2026-06-04-s6c-act-1-integral-sq-exp-neg-sq.md` for the full
ACT report (proof structure, bearer recheck, PREP-3 risk register replay,
linter notes).

**S6c ACT-2 (next research claim)**: ship `complex_gaussian_integral_norm_sq`
(~15-20 LOC, 1-D complex moment via `Complex.measurableEquivRealProd` +
Fubini, leveraging the new `integral_sq_exp_neg_sq`) and
`schur_orthogonality_complex_gaussian_diag` (~25-35 LOC, n-dim diagonal
Schur via `integral_fintype_prod_volume_eq_prod`). Route unchanged from
PREP-2 §3.2-3.3 and PREP-3 §5; no further PREP needed before ACT-2.

**Pre-ACT-1 gate**: host disk must be GREEN (≥5 Gi free) before launching the
Docker rebuild. At PREP-3 time `df -h /Users/rwalters` reports 100% capacity,
2.0Gi free — unsafe for a 3000+-job rebuild.

**Deferred (orthogonal to S6c, multi-week)**:

- **S6d (Mathlib milestone — `Measure ℚ_p` with `μ(ℤ_p) = 1`)**: multi-week
  upstream Mathlib PR. Tracked in S4b survey #18269. The standard
  `ψ_p : ℚ_p → ℂ` additive character contribution is heavier still.
- **n-dim ℂ Fourier-Gaussian lift**: the n-dim version of
  `complex_fourier_gaussian_pi` (current proof is 1-dim only).
  Independent of S6c; Path B (per-axis Fubini) likely carries
  through directly given the S6 ACT precedent.

## Open Blockers

- None on the archimedean side. All required Mathlib infrastructure
  for S6b (and S6c, S6 family) is verified to be present at
  `lake-manifest` SHA `2df2f0150c…` v4.26.0 by the S6b/S6c PREPs and
  this S11 PREP's bearer recheck (§3 of the sessions memo).
- p-adic case (C1, C2, C3) blocks on two missing Mathlib pieces:
  standard additive character `ψ_p : ℚ_p → ℂ` and explicit Haar
  measure on `ℚ_p` with `μ(ℤ_p) = 1`. Neither lands in this slug
  directly — they are S6d upstream Mathlib milestones.
- **Host disk infra (INFRA-only, not math)**: was a concern at S11 PREP
  time; S6b ACT-2 (2026-05-31) successfully ran a full Docker rebuild
  (3129/3129 jobs). This blocker is currently RESOLVED but worth
  re-checking before any S6c ACT cycle that may need a fresh
  3000+-job rebuild.

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
- `state.md` — this file (rewritten by S11 PREP; refreshed by S6c PREP-3 this PR)
- `sessions/2026-05-16-s11-prep-s6b-sharpened.md` — S11 PREP detail (~350 LOC; primary reference for S6b ACT)
- `sessions/2026-05-31-s6b-act-complex-fourier-gaussian.md` — S6b ACT session report (PR #21575)
- `sessions/2026-05-31-s6b-act-2-deferred-companions.md` — S6b ACT-2 session report (PR #21779)
- `sessions/2026-06-02-s6c-prep-3-gaussianreal-variance-skeleton.md` — S6c PREP-3 (this PR; bearer recheck @ `2df2f0150c` + paste-ready ACT-1 skeleton for `integral_sq_exp_neg_sq`)

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
