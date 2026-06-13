# Current State

**Phase**: RESEARCH
**Since**: 2026-06-09T00:00:00Z (S6c ACT-2 merged: diagonal Schur orthogonality)
**Iteration**: 17 (S6c PREP-4 + STATE-SYNC — diagonal Schur complete; off-diagonal ACT-3 seeded)

> **STATE-SYNC note (researcher-2, 2026-06-13):** this file had drifted to
> iteration 6 (S6 ACT) while the JSON tracker
> (`src/data/research/problems/area-of-circle-oq-05-oq-04.json`) and the
> source advanced to iteration 17. PR #23179 forward-synced the JSON but
> left state.md behind. This sync brings state.md into agreement with the
> JSON tracker and with origin/main source
> (`proofs/Proofs/AreaOfCircleOQ05OQ04.lean`, **1114 LOC, 28 public
> theorems + 4 private helpers, 0 sorries, 0 axioms**, verified against
> origin/main). Doc-only; 0 Lean lines; no Docker build (host Docker down
> 2026-06-13).

## Current Focus

The "over ℂ" archimedean programme is built out through **S6c ACT-2**.
On top of the S6 n-dimensional shifted Gaussian, the source now also
delivers the complex Fourier-Gaussian eigenfunction (S6b, Parts 6–7) and
the second-moment / diagonal Schur-orthogonality results (S6c ACT-1/ACT-2,
Parts 8–9):

- **S6b ACT (Parts 6–7):** the complex Gaussian is a Fourier
  eigenfunction — `complex_fourier_gaussian_pi`,
  `complex_fourier_gaussian`, `complex_fourier_gaussian_normSq`, plus the
  shifted/modulation companion `complex_fourier_gaussian_shifted` and the
  normalised density eigenfunction `complex_fourier_gaussian_density_eigen`
  (eigenvalue `1`). This is the load-bearing archimedean analogue of the
  intended p-adic self-Fourier identity (C2).
- **S6c ACT-1 (Part 8):** `integral_sq_exp_neg_sq` — the 1-D real second
  moment `∫ x²·exp(-x²) = √π/2`, via the `gaussianReal 0 (1/2 : ℝ≥0)`
  variance shortcut (#22316, merged 2026-06-05).
- **S6c ACT-2 (Part 9):** `complex_gaussian_integral_norm_sq` (1-D complex
  second moment `∫_ℂ ‖w‖²·exp(-‖w‖²) = π`) and
  `schur_orthogonality_complex_gaussian_diag` (n-dim diagonal Schur
  orthogonality `∫_{ℂⁿ} ‖z_i‖²·(1/π)ⁿ·exp(-∑‖z_k‖²) = 1` for `i : Fin n`),
  with 2 private integrability helpers (#22549, merged 2026-06-06).

The underlying S6 ACT result — **n-dimensional translation invariance** of
the parametric complex Gaussian, for any `n : ℕ`, `b > 0`, shift vector
`c : Fin n → ℂ` —

    ∫_{Fin n → ℂ} exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) dz = (π / b)ⁿ

remains in place (Part 5), generalising both S4a (n-dim unshifted, `c = 0`)
and S5 (1-D shifted, `n = 1`), and unlocking the canonical n-dimensional
two-parameter complex Gaussian density

    ∫_{Fin n → ℂ} (b/π)ⁿ · exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) dz = 1.

## Built (Lean)

In `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (**1114 LOC, 28 public
theorems + 4 private helpers**). The S6 additions live in `Part 5`:

- `complex_gaussian_integral_scaled_pow_shifted_norm {n} (b > 0)
    (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) = (π / b)ⁿ`
  — main n-dim shifted theorem (S6a Path B per
  `s6a-prep-pi-haar-vs-fubini.md`).
- `complex_gaussian_integral_scaled_pow_shifted_normSq {n} (b > 0)
    (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, exp(-(b · ∑ᵢ normSq (zᵢ - cᵢ))) = (π / b)ⁿ`
  — `Complex.normSq` form via `simp_rw [Complex.normSq_eq_norm_sq]`.
- `complex_gaussian_integral_pow_unit_shifted_norm {n} (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, exp(-∑ᵢ ‖zᵢ - cᵢ‖²) = πⁿ`
  — `b = 1` corollary; bridges to `complex_gaussian_integral_pow_unit_norm`
  (the `c = 0` case).
- `complex_gaussian_density_pow_shifted {n} (b > 0) (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, (b/π)ⁿ · exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) = 1`
  — canonical n-dim two-parameter complex Gaussian probability density.

The full S5 family (1-D shifted) remains in place from the prior ACT
and is exactly the `n = 1` reduction of the new theorems.

No new imports. The proof relies on `integral_fintype_prod_volume_eq_prod`
from `Mathlib.MeasureTheory.Integral.Pi` (already imported), the S5
shifted theorem `complex_gaussian_integral_scaled_shifted_norm`, and
standard `Finset` / `Real.exp_sum` simp lemmas.

All proofs are sorry-free, axiom-free. Each new theorem strictly
generalises the previous S4a + S5 work:

| New theorem | Reduces to (at `c = 0`) | Reduces to (at `n = 1`) |
|---|---|---|
| `..._scaled_pow_shifted_norm` | `..._scaled_pow` (S4a) | `..._scaled_shifted_norm` (S5) |
| `..._scaled_pow_shifted_normSq` | `..._scaled_pow_normSq` (S4a) | `..._scaled_shifted` (S5) |
| `..._pow_unit_shifted_norm` | `..._pow_unit_norm` (S4a) | `..._unit_shifted_norm` (S5) |
| `..._density_pow_shifted` | `..._pow_normalised` (S4a) | `..._density_shifted` (S5) |

### S6b ACT (Parts 6–7): complex Fourier-Gaussian eigenfunction

- `complex_fourier_gaussian (b) (hb : 0 < b.re) (w)` — parametric
  Fourier-Gaussian.
- `complex_fourier_gaussian_pi (w)` — self-Fourier eigenfunction at
  `b = π` (load-bearing archimedean analogue of (C2)).
- `complex_fourier_gaussian_normSq` — `Complex.normSq` form.
- `complex_fourier_gaussian_shifted (b) (hb) (x w)` — modulation companion
  (direct `_root_.fourier_gaussian_innerProductSpace'` specialisation at
  `V := ℂ`).
- `complex_fourier_gaussian_density_eigen (w)` — the normalised density
  `(1/π) · exp(-π · ‖z‖²)` is a Fourier eigenfunction with eigenvalue `1`.

### S6c ACT-1/ACT-2 (Parts 8–9): second moments + diagonal Schur

- `integral_sq_exp_neg_sq` — 1-D real second moment `∫ x²·exp(-x²) = √π/2`,
  via `gaussianReal 0 (1/2 : ℝ≥0)` variance shortcut (S6c ACT-1, #22316).
- `complex_gaussian_integral_norm_sq` — 1-D complex second moment
  `∫_ℂ ‖w‖²·exp(-‖w‖²) = π` (S6c ACT-2, #22549).
- `schur_orthogonality_complex_gaussian_diag {n} (i : Fin n)` — n-dim
  diagonal Schur orthogonality
  `∫_{ℂⁿ} ‖z_i‖²·(1/π)ⁿ·exp(-∑‖z_k‖²) = 1` (S6c ACT-2, #22549), plus 2
  private integrability helpers.

## Status

- Sorries: 0 (the 3 `sorry` tokens in the file are the prose phrase
  "sorry-free" in docstrings, not code).
- Axioms: 0.
- File: 1114 LOC, 28 public theorems + 4 private helpers (verified against
  origin/main, 2026-06-13).
- Build: the merged S6/S6b/S6c PRs (incl. #22316, #22549) were Docker-built
  when they landed pre-blackout. This STATE-SYNC ships no Lean change and
  was **not** re-built — host Docker is down (2026-06-13). A confirmatory
  `./proofs/scripts/docker-build.sh Proofs.AreaOfCircleOQ05OQ04` should be
  run when Docker returns.

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Markdown set + three-statement repair | 0 Lean | merged |
| S2a | ACT-A | `complex_gaussian_integral` (b = π) | ~120 | merged |
| S3 | ACT-B | Parametric in `b > 0` + 3 corollaries | ~120 | merged |
| S4a | ACT | n-dim `∫_{ℂⁿ} exp(-b·∑‖zᵢ‖²) = (π/b)ⁿ` + 3 corollaries | ~96 | open (#18221) |
| S4b | OBSERVE | p-adic Mathlib gap survey (doc-only) | 0 Lean | open (#18269) |
| S5 | ACT | Translation invariance + `(c, b)`-density | ~110 | merged |
| S6a PREP | PREP | Route audit: pi-Haar (A) vs Fubini (B) | 0 Lean | merged (#18389) |
| S6b PREP | PREP | Complex Fourier-eigenfunction route | 0 Lean | merged (#18422) |
| S6c PREP | PREP | Schur orthogonality via parametric differentiation | 0 Lean | merged (#18488) |
| S6c PREP-2 | PREP | Mathlib moment-shortcut obsoletes S6c | 0 Lean | merged (#18584) |
| S6 | ACT | n-dim shifted Gaussian + 3 corollaries (Path B) | ~115 | merged |
| S6b | ACT | Complex Fourier-Gaussian eigenfunction (Parts 6–7) | ~110 | merged |
| S6c ACT-1 | ACT | `integral_sq_exp_neg_sq` (1-D real 2nd moment, Part 8) | ~16 | merged (#22316) |
| S6c ACT-2 | ACT | Complex 2nd moment + diagonal Schur (Part 9) | ~125 | merged (#22549) |
| S6c PREP-4 | PREP | Off-diagonal Schur ACT-3 skeleton | 0 Lean | seeded |

## Next Action

The "over ℂ" programme is complete through diagonal Schur orthogonality.
Remaining work is **Docker-gated** (host Docker down 2026-06-13) — see the
blocked flag below.

- **S6c ACT-3 (off-diagonal Schur)** — requires Docker GREEN:
  `schur_orthogonality_complex_gaussian_off_diag {n} (i j) (hij : i ≠ j) :
  ∫_{ℂⁿ} conj(z_i)·z_j·(1/π)ⁿ·exp(-∑‖z_k‖²) = 0`, via per-axis Fubini
  (`integral_fintype_prod_volume_eq_prod`, reused from ACT-2) + 1-D
  odd-symmetry collapse. Single new bearer to confirm:
  `real_odd_x_exp_neg_sq : ∫ x, x·exp(-x²) = 0` (three candidate routes in
  PREP-4 §3.1). Paste-ready skeleton in PREP-4 §4. ~80–110 LOC.
- **S6d (Mathlib milestone — `Measure ℚ_p`)**: the explicit
  `MeasureTheory.Measure ℚ_p` instance with `μ(ℤ_p) = 1` plus the standard
  C-valued additive character `ψ_p : ℚ_p → ℂ`, from the S4b survey, to
  formalise the original p-adic self-Fourier identity (C2). Multi-week
  upstream PR; not absent-Docker work.

## Blocked (2026-06-13)

Flagged **blocked** during the host-Docker blackout. All in-scope "over ℂ"
deliverables (S2a–S6c ACT-2) are merged and sorry-/axiom-free on
origin/main. The only remaining steps — S6c ACT-3 (off-diagonal Schur) and
S6d (p-adic Mathlib milestone) — both require a working Lean build to
verify, which is unavailable while Docker is down. Re-open when Docker
returns; ACT-3 has a paste-ready PREP-4 skeleton.

## Attempt Counts

- Sessions to date: S1 OBSERVE, S2a ACT-A, S3 ACT-B, S4a ACT, S4b OBSERVE,
  S5 ACT, S6a PREP, S6b PREP, S6c PREP, S6c PREP-2, S6 ACT, S6b ACT,
  S6c ACT-1 (#22316), S6c ACT-2 (#22549), S6c PREP-4, and STATE-SYNC
  forward-syncs (JSON #23179; this state.md sync, researcher-2 2026-06-13).
- Next ACT (S6c ACT-3, off-diagonal Schur) is Docker-gated — see Blocked.
- Approaches tried (selected):
  - S1: OBSERVE — three-candidate repair scaffolding.
  - S2a: ACT-A — `b = π` complex Gaussian via Fubini + measurable equivalence.
  - S3: ACT-B — parametric Fubini, identical skeleton, generalised in `b`.
  - S4a: ACT — `exp(-∑) = ∏ exp` reduction + n-fold Fubini
    (`integral_fintype_prod_volume_eq_pow`), per-axis factor by S3.
  - S5: ACT — `integral_add_right_eq_self` + `complex_gaussian_integral_scaled_norm`,
    shifting `z - c → z + (-c)` to match the additive-translation form.
    First proof attempt failed at `rw [integral_add_right_eq_self]` (HOU
    can't pattern-match `?f (x + ?g)` through a lambda); fixed by
    chaining via `.trans` with the explicit `f := fun w => exp(-(b·‖w‖²))`.
  - S6 ACT: Path B per S6a PREP. Heterogeneous Fubini
    via `integral_fintype_prod_volume_eq_prod` (verified at v4.26.0 pin
    `2df2f015...` at `Mathlib/MeasureTheory/Integral/Pi.lean:114`),
    `Real.exp_sum` factoring chain identical to S4a, per-axis collapse
    via the S5 shifted theorem. Docker build succeeded at merge time
    (3123/3123 jobs, no new warnings).
  - S6b ACT: complex Fourier-Gaussian eigenfunction via ℂ ≃ ℝ × ℝ
    transport of `Real.fourierIntegral_gaussian_pi` + the shifted
    modulation companion (Parts 6–7).
  - S6c ACT-1/ACT-2: second moments via the `gaussianReal` variance
    shortcut, then diagonal Schur orthogonality by per-axis Fubini
    collapse (Parts 8–9, #22316 / #22549).
