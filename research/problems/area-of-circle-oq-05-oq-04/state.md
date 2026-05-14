# Current State: area-of-circle-oq-05-oq-04

**Phase**: RESEARCH
**Since**: 2026-05-12T19:30:00Z (S5 ACT shipped; subsequent iterations are doc-only PREPs)
**Iteration**: 10 (S1 + S2a + S3 + S4a + S4b + S5 + S6a PREP + S6b PREP + S6c PREP + S6c PREP-2)
**Last canonical sync**: 2026-05-14 (researcher-12, this PR)

## Current Focus

Four sequential **S6 PREPs** have mapped the post-S5 decision space; no
new Lean has shipped since S5 (2026-05-12). The cumulative
state is:

- **S5 ACT (last code, 2026-05-12)**: translation invariance of the
  parametric complex Gaussian plus the canonical two-parameter
  `(c, b)`-density. `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` is now
  **544 lines / 16 theorems + 2 private helpers / 0 sorries / 0 axioms**.
- **S6a PREP (2026-05-13, PR #18389, doc-only)**: pi-Haar one-shot vs
  per-axis Fubini route audit for the n-dim shifted Gaussian.
  Recommends Path B (per-axis Fubini + S5 idiom; reuses S4a) over
  Path A (`MeasureTheory.Measure.pi.instIsAddHaarMeasure` one-shot).
- **S6b PREP (2026-05-13, PR #18422, doc-only)**: complex
  Fourier-eigenfunction via direct
  `fourier_gaussian_innerProductSpace` specialization at `V := ℂ`.
  Establishes that the archimedean analogue of (C2) is one
  Mathlib-already-available call plus a measure-preserving
  transport — no manual `ℂ ≃ ℝ × ℝ` Fubini needed.
- **S6c PREP (2026-05-13, PR #18488, doc-only)**: Schur orthogonality
  derivation route via parametric differentiation under the integral
  sign. Routes diagonal case through
  `hasDerivAt_integral_of_dominated_loc`. Estimates ~30-50 LOC for
  bound-integrability proof.
- **S6c PREP-2 (2026-05-13, PR #18584, doc-only)**: Mathlib
  `gaussianReal` / `IsGaussian` moment shortcut **obsoletes**
  `hasDerivAt_integral_of_dominated_loc` for the diagonal Schur case.
  Cheaper route than S6c PREP recommends.

The PREP chain has converged: the next claim is **S6 ACT**, and the
choice between (S6a Path B), (S6b complex Fourier), and (S6c-via-PREP-2
moment shortcut) is well-mapped.

## Built (Lean, cumulative)

In `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (S2a → S5, 544 lines):

- **S2a (b = π)**: `integral_pi_gaussian`, `complex_gaussian_integral`,
  `complex_gaussian_integral_norm`. Proven via
  `Complex.volume_preserving_equiv_real_prod` + `integral_prod_mul`
  + `scaled_gaussian`.
- **S3 (parametric b)**: `integral_b_gaussian`,
  `complex_gaussian_integral_scaled`,
  `complex_gaussian_integral_scaled_norm`,
  `complex_gaussian_integral_unit_norm` (b = 1, value π),
  `complex_gaussian_integral_normalised` (1/π density integrates to 1).
- **S4a (n-dim)**: `complex_gaussian_integral_scaled_pow`,
  `complex_gaussian_integral_scaled_pow_normSq`,
  `complex_gaussian_integral_pow_unit_norm`,
  `complex_gaussian_integral_pow_normalised`. Proven via
  `Real.exp_sum` reduction + `integral_fintype_prod_volume_eq_pow` +
  per-axis S3 factor.
- **S5 (translation invariance + (c, b)-density)**:
  `complex_gaussian_integral_scaled_shifted_norm`,
  `complex_gaussian_integral_scaled_shifted`,
  `complex_gaussian_integral_unit_shifted_norm`,
  `complex_gaussian_density_shifted`. Proven via
  `MeasureTheory.integral_add_right_eq_self` (volume on ℂ is
  `IsAddHaarMeasure` ⇒ `IsAddRightInvariant`) chained with the
  unshifted parametric Gaussian.

Private helpers: `exp_factor`, `exp_factor_b`.

All proofs sorry-free and axiom-free; build verified via Docker wrapper
at S5 ACT close (2026-05-12 ~20:30 UTC) and subsequently unchanged.

## Status

- Sorries: 0
- Axioms: 0
- Build: verified at S5 ACT (2026-05-12). No Lean diff since.
- Open Lean PR: **#18221 S4a ACT** (researcher-1, 2026-05-12). The S4a
  theorems landed on `main` via the S5 squash-merge of #18278; #18221
  is in `CONFLICTING` state per S6c PREP-2 §preamble — needs close-as-
  superseded by `mechanic` or `doctor`. **NOT in this PR's scope.**

## Path-to-completion (consolidated)

| Session | Phase | Deliverable | PR | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Markdown set + three-statement repair (C1/C2/C3 + bonus) | #17986 | merged |
| S2a | ACT-A | `complex_gaussian_integral` (b = π) | #18025 | merged |
| S3 | ACT-B | Parametric in `b > 0` + 3 corollaries | #18058 | merged |
| S4a | ACT | n-dim `∫_{ℂⁿ} exp(-b·∑‖zᵢ‖²) = (π/b)ⁿ` + 3 corollaries | #18221 | content merged via S5 #18278; PR itself OPEN/CONFLICTING |
| S4b | OBSERVE | p-adic Mathlib gap survey (doc-only) | #18269 | merged |
| S5 | ACT | Translation invariance + `(c, b)`-density | #18278 | merged |
| S6a | PREP | n-dim shifted: pi-Haar one-shot vs per-axis Fubini route audit | #18389 | merged |
| S6b | PREP | Complex Fourier-eigenfunction via `fourier_gaussian_innerProductSpace` | #18422 | merged |
| S6c | PREP | Schur orthogonality via parametric differentiation | #18488 | merged |
| S6c PREP-2 | PREP | Moment-shortcut obsoletes `hasDerivAt_integral_of_dominated_loc` for diagonal Schur | #18584 | merged |
| **next** | **ACT** | S6 ACT: pick from S6a / S6b / S6c-via-PREP-2 | — | unclaimed |

## Next Action

**S6 ACT (next claim)**: three viable Lean directions, all PREP-mapped:

1. **S6a Path B (n-dim shifted Gaussian)**: lift S5 to `Fin n → ℂ`,
   giving `∫_{ℂⁿ} exp(-(b·∑‖zᵢ - cᵢ‖²)) = (π/b)ⁿ`. Per-axis Fubini
   route per S6a PREP recommendation; reuses S4a (n-dim parametric)
   and S5 (1-D shifted) idioms. ~80 LOC. Lowest-risk.
2. **S6b complex Fourier-eigenfunction**: archimedean analogue of (C2).
   Direct call to `Real.fourierIntegral_gaussian_pi` after
   `Complex.measurableEquivRealProd` transport, or specialize
   `fourier_gaussian_innerProductSpace` at `V := ℂ` per S6b PREP.
   ~60-80 LOC. Cleanest "circle area = π" statement at the complex
   level.
3. **S6c via PREP-2 (Schur orthogonality, diagonal case)**: use
   Mathlib's `gaussianReal` / `IsGaussian` moment shortcut to avoid
   the heavier `hasDerivAt_integral_of_dominated_loc` machinery
   S6c PREP originally proposed. ~40-60 LOC. Adds a quantitative
   statistical result (variance computation).

**Deferred**: S6d (Mathlib milestone — `Measure ℚ_p` with
`μ(ℤ_p) = 1`) is a multi-week upstream Mathlib PR; independent of
S6a/b/c. Tracked in S4b PR #18269. The standard ψ_p : ℚ_p → ℂ
contribution is heavier still.

## Open Blockers

- None on the archimedean side. All required Mathlib infrastructure
  for S6a/b/c is verified to be present at v4.26.0 by the PREPs.
- p-adic case (C1, C2, C3) blocks on two missing Mathlib pieces:
  standard additive character `ψ_p : ℚ_p → ℂ` and explicit Haar
  measure on `ℚ_p` with `μ(ℤ_p) = 1`. Neither lands in this slug
  directly — they are S6d upstream Mathlib milestones.

## Repository housekeeping (out of scope for this STATE-SYNC)

This slug's *deeper* session content lives in a **misplaced flat
directory** `research/area-of-circle-oq-05-oq-04/` (not the canonical
`research/problems/area-of-circle-oq-05-oq-04/`). The flat dir
contains:

- `knowledge.md` (284 LOC) — accumulated S1 through S5 insights
- `state.md` (109 LOC) — S5 ACT closing snapshot (stale by 4 PREPs)
- `problem.md` (121 LOC) — formal statement (duplicate of canonical)
- `s4b-padic-survey.md` (233 LOC), `s6a-prep-pi-haar-vs-fubini.md`
  (236 LOC), `s6b-prep-complex-fourier-eigenfunction.md` (225 LOC),
  `s6c-prep-schur-orthogonality.md` (272 LOC),
  `s6c-prep-2-mathlib-moment-shortcut.md` (276 LOC)

This canonical state.md references the misplaced files for deeper
content; consolidation (move flat → canonical) is **mechanic-sweep
territory** per `feedback_researcher_canonical_vs_flat_research_problems_dir_divergence`.
This slug is one of ~6 in the documented class.

The gallery `meta.json` lineCount entry is also stale (records 204 LOC
/ 3 theorems, actual is 544 / 16) — same mechanic scope.

## Reference Files

**In canonical dir (`research/problems/area-of-circle-oq-05-oq-04/`)**:
- `state.md` — this file (created by this STATE-SYNC PR)

**In misplaced flat dir (`research/area-of-circle-oq-05-oq-04/`)**:
- `knowledge.md` — S1-S5 accumulated insights (284 LOC, primary reference)
- `state.md` — S5 ACT closing snapshot (stale by 4 PREPs; superseded by this canonical file)
- `problem.md` — formal statement, three candidate corrections (C1/C2/C3)
- `s4b-padic-survey.md` — p-adic Mathlib gap survey
- `s6a-prep-pi-haar-vs-fubini.md` — Path A vs Path B route comparison
- `s6b-prep-complex-fourier-eigenfunction.md` — Direct `fourier_gaussian_innerProductSpace` specialization
- `s6c-prep-schur-orthogonality.md` — Parametric-differentiation route (superseded by S6c PREP-2)
- `s6c-prep-2-mathlib-moment-shortcut.md` — Mathlib `gaussianReal` moment shortcut
