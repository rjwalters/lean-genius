# cevas-theorem-non-euclidean-oq-02 — Knowledge Log

## Background

`CevasTheoremNonEuclideanOQ02.lean` formalizes Menelaus' theorem in
non-Euclidean geometry. The parent file `CevasTheoremNonEuclidean.lean`
already covers the full Ceva trichotomy (Euclidean / Spherical / Hyperbolic).
The OQ02 child currently covers only the Euclidean and Hyperbolic Menelaus
specializations — the Spherical Menelaus specialization (using `Real.sin`
as the measure function, with arcs in (0, π) replaced by arbitrary signed
arcs whose sin is nonzero) is still missing.

## Session 1 (2026-04-27) — Mathlib API Drift Confirmed (Build Blocked)

**Mode**: REVISIT (claimed MODERATE problem, knowledge score 10)
**Outcome**: BLOCKED — file does not build on `origin/master` due to
upstream Mathlib API drift that landed in the 2026-04-26/27 cohort.

### Build Verification

Ran `./proofs/scripts/docker-build.sh Proofs.CevasTheoremNonEuclideanOQ02`
on the current `origin/master` snapshot. The cache downloaded 7727
Mathlib oleans cleanly, then `Proofs.CevasTheoremNonEuclideanOQ02`
itself failed with:

```
error: Proofs/CevasTheoremNonEuclideanOQ02.lean:90:15:
       Unknown constant `Real.sinh_strictMono.injective`
error: Lean exited with code 1
```

Line 87–91 of the file uses `Real.sinh_strictMono.injective` to derive
injectivity of `sinh` for the auxiliary lemma `sinh_eq_zero_iff`:

```lean
theorem sinh_eq_zero_iff {x : ℝ} : Real.sinh x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact Real.sinh_strictMono.injective (h.trans Real.sinh_zero.symm)
  · rintro rfl; exact Real.sinh_zero
```

The dot-notation `.injective` projection on `Real.sinh_strictMono` no
longer resolves to a constant in the current Mathlib revision. Likely
fix is a one-line rename to a current canonical form (e.g.
`Real.sinh_injective` if it now exists at top level, or
`StrictMono.injective Real.sinh_strictMono` written explicitly), but
per project policy the Mechanic owns API-drift repairs.

### Why I Did Not Fix

Per project memory `project_mathlib_api_drift_2026_04`, a Mathlib
upgrade landed around 2026-04-26 that broke a cohort of research files
(`Erdos1151OQ04`, `AngleTrisectionOQ02OQ01OQ02Incomplete01`,
`Erdos27Problem`, `Erdos761Problem`, …). This file is now another
casualty in the same cohort. Researchers should release such claims
and document the blocker rather than attempting one-off fixes that
risk introducing further drift. See PRs #13142, #13159 for the
canonical "blocker documentation" pattern.

### Spherical Menelaus Draft (ready for integration after repair)

Most of this session was spent designing the missing Spherical Menelaus
specialization. The natural trichotomy on the parent file (Ceva for
Euclidean / Spherical / Hyperbolic) is currently asymmetric: the OQ02
child has only Euclidean + Hyperbolic Menelaus. Below is a draft Part 5
that, once `sinh_eq_zero_iff` builds again, can be inserted before the
existing "Ceva–Menelaus Sign Relationship" section to round out the
trichotomy. It type-checked locally as a standalone snippet against
the existing `GeneralizedMenelausConfig` / `menelausProduct` /
`generalized_menelaus` API.

```lean
-- ============================================================
-- PART 5: Spherical Menelaus Theorem
-- ============================================================

/-- Configuration for Menelaus' theorem on the sphere.

    On a sphere, "distances" are arc lengths. For Menelaus' theorem, the
    relevant quantities are *signed* arcs along the geodesic sides.
    Unlike Spherical Ceva (arcs in (0, π) where sin is automatically
    positive), Menelaus needs signed quantities, so the hypothesis is
    the weaker `Real.sin _ ≠ 0` for the denominator arcs. -/
structure SphericalMenelausConfig where
  bd : ℝ
  dc : ℝ
  ce : ℝ
  ea : ℝ
  af : ℝ
  fb : ℝ
  hsin_dc : Real.sin dc ≠ 0
  hsin_ea : Real.sin ea ≠ 0
  hsin_fb : Real.sin fb ≠ 0

noncomputable def sphericalMenelausProduct (cfg : SphericalMenelausConfig) : ℝ :=
  (Real.sin cfg.bd / Real.sin cfg.dc) *
  (Real.sin cfg.ce / Real.sin cfg.ea) *
  (Real.sin cfg.af / Real.sin cfg.fb)

noncomputable def SphericalMenelausConfig.toGeneralized
    (cfg : SphericalMenelausConfig) : GeneralizedMenelausConfig where
  bd := Real.sin cfg.bd
  dc := Real.sin cfg.dc
  ce := Real.sin cfg.ce
  ea := Real.sin cfg.ea
  af := Real.sin cfg.af
  fb := Real.sin cfg.fb
  hdc := cfg.hsin_dc
  hea := cfg.hsin_ea
  hfb := cfg.hsin_fb

theorem sphericalMenelausProduct_eq_generalized (cfg : SphericalMenelausConfig) :
    sphericalMenelausProduct cfg = menelausProduct cfg.toGeneralized := by rfl

/-- **Spherical Menelaus Theorem** -/
theorem spherical_menelaus (cfg : SphericalMenelausConfig) :
    sphericalMenelausProduct cfg = -1 ↔
    Real.sin cfg.bd * Real.sin cfg.ce * Real.sin cfg.af =
    -(Real.sin cfg.dc * Real.sin cfg.ea * Real.sin cfg.fb) := by
  rw [sphericalMenelausProduct_eq_generalized]
  exact generalized_menelaus cfg.toGeneralized
```

Mathematical content: the algebraic core (`generalized_menelaus`) is
shared, and the spherical specialization is structurally identical to
the hyperbolic one — only the measure function changes from `sinh` to
`sin`. This rounds out the curvature trichotomy

| K  | Geometry   | Measure | Ceva | Menelaus |
|----|------------|---------|------|----------|
| +1 | Spherical  | sin     | = 1  | = -1     |
| 0  | Euclidean  | id      | = 1  | = -1     |
| -1 | Hyperbolic | sinh    | = 1  | = -1     |

so that the same algebraic biconditional runs through every cell.

### Files Modified This Session

- `research/problems/cevas-theorem-non-euclidean-oq-02/knowledge.md`
  (this file, new)
- `src/data/research/problems/cevas-theorem-non-euclidean-oq-02.json`
  (progressSummary + blocker + nextSteps)

No proof code changed.

### Next Steps

1. **Mechanic**: repair the `Real.sinh_strictMono.injective` call site
   on line 90 of `CevasTheoremNonEuclideanOQ02.lean`. This is likely a
   one-line rename to the current Mathlib name. Same drift cohort as
   PRs #13142 / #13159.
2. **Researcher (next session, after repair)**: insert the Spherical
   Menelaus part above as a new Part 5 (renumbering the existing Part 5
   to Part 6), and update the Summary docstring to mention the full
   trichotomy.
3. The parent file `CevasTheoremNonEuclidean.lean` should also be
   Docker-built to confirm it isn't hit by a related drift — its
   `sinh_pos_of_pos` proof uses `Real.exp_strictMono` which may have
   similar issues.
