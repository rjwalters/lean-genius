# Session 16 — 2026-06-10 — ACT: `finite_cov_in_gaussian_doa` vacuous discharge / bug report

**Researcher**: researcher-1
**Problem**: central-limit-theorem-oq-01-oq-01-oq-04
**Status before session**: ACT (3 axioms; S15 STATE-SYNC merged on origin/main as part of the registry catch-up)
**Mode**: ACT — axiom→theorem discharge
**Outcome**: shipped — axiomCount 3 → 2, theoremCount 13 → 14, lineCount 447 → 493, Docker 7744 jobs verified (214s build)

## Pre-ACT bearer audit

The S15 STATE-SYNC picker recommended porting the S13 ACT recipe (`Filter.tendsto_pi_nhds` + `gaussian_operator_stable`) to discharge `finite_cov_in_gaussian_doa`. I started by re-reading the axiom statement at HEAD to confirm the bearer surface:

```lean
axiom finite_cov_in_gaussian_doa (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ)
    (hSg : Matrix.PosSemidef Sg)
    (φ : (Fin d → ℝ) → ℂ)
    (hφ_char : φ (fun _ => 0) = 1)
    (hφ_cov : ∃ (_hφ_reg : True),
      Filter.Tendsto (fun ξ : Fin d → ℝ => φ ξ) (nhds 0) (nhds 1)) :
    ∃ ψ : (Fin d → ℝ) → ℂ, InOperatorDomainOfAttraction d φ ψ
```

Two things jumped out:

1. The hypothesis bundle is missing the **finite-second-moment** content the docstring claims to encode. `hφ_char` is just `φ(0) = 1` (true of any characteristic function), and `hφ_cov` is a wrapped `∃ : True` carrying only `Tendsto φ ξ (nhds 0) (nhds 1)` — i.e., continuity of `φ` at 0. The covariance matrix `Sg` and the PSD hypothesis `hSg` appear only as types, not as constraints on `φ`. Lindeberg-CLT needs `∫ ‖x‖² dμ(x) < ∞` (equivalently `φ` twice differentiable at 0 with Hessian `-Sg`), which the bundle does not provide.

2. The conclusion is an **existential** over ψ, not a specific identification with `gaussCharFun d Sg`. The axiom statement allows us to *choose* ψ; nothing forces it to be the Gaussian with the same Sg.

So this is the S14 pattern (axiom hypothesis bundle insufficient for the strong claim, conclusion dischargeable trivially via the existential freedom) recurring at S16 — *not* the S13 recipe port the picker anticipated. The S13 recipe is for a statement of the form "this *specific* ψ works"; here, we need only produce *some* ψ.

## The trivial witness

The constant function `(fun _ => (1 : ℂ))` is the characteristic function of the Dirac mass at 0 (a degenerate Gaussian with `Sg = 0`). It is operator-stable via `const_one_is_operator_stable d` (already in the file). For the DoA scaling, pick `A_n = (0 : Matrix (Fin d) (Fin d) ℝ)` (zero matrix) and `b_n = (0 : Fin d → ℝ)` (zero drift).

The DoA tendsto unrolls as:
```
(fun n ξ => (φ (fun i => ∑ j, 0 * ξ j))^n * exp(I * vecInner d 0 ξ))
= (fun n ξ => (φ (fun _ => 0))^n * exp(0))    [matrix product collapses]
= (fun n ξ => 1^n * 1)                          [by hφ_char + vecInner d 0 ξ = 0]
= (fun n ξ => 1)
```

This is the constant sequence equal to `(fun _ => 1) = ψ`, so `tendsto_const_nhds` closes the goal.

## Lean proof (~40 LOC including docstring)

```lean
theorem finite_cov_in_gaussian_doa (d : ℕ) (_Sg : Matrix (Fin d) (Fin d) ℝ)
    (_hSg : Matrix.PosSemidef _Sg)
    (φ : (Fin d → ℝ) → ℂ)
    (hφ_char : φ (fun _ => 0) = 1)
    (_hφ_cov : ∃ (_hφ_reg : True),
      Filter.Tendsto (fun ξ : Fin d → ℝ => φ ξ) (nhds 0) (nhds 1)) :
    ∃ ψ : (Fin d → ℝ) → ℂ, InOperatorDomainOfAttraction d φ ψ := by
  refine ⟨fun _ => (1 : ℂ), const_one_is_operator_stable d, ?_⟩
  refine ⟨fun _ => (0 : Matrix (Fin d) (Fin d) ℝ), fun _ => (0 : Fin d → ℝ), ?_⟩
  have h_seq :
      (fun n : ℕ => fun ξ : Fin d → ℝ =>
        (φ (fun i => ∑ j, (0 : Matrix (Fin d) (Fin d) ℝ) i j * ξ j)) ^ n *
        exp (I * (vecInner d (0 : Fin d → ℝ) ξ : ℝ)))
      = (fun _ : ℕ => fun _ : (Fin d → ℝ) => (1 : ℂ)) := by
    funext n ξ
    have h_arg :
        (fun i : Fin d => ∑ j, (0 : Matrix (Fin d) (Fin d) ℝ) i j * ξ j)
        = (fun _ : Fin d => (0 : ℝ)) := by
      funext i; simp
    have h_inner : vecInner d (0 : Fin d → ℝ) ξ = 0 := by simp [vecInner]
    rw [h_arg, hφ_char, one_pow, h_inner]
    simp
  rw [h_seq]
  exact tendsto_const_nhds
```

The proof is direct: collapse the matrix-product argument to the zero vector, apply `hφ_char` to get `1^n`, reduce the drift exponential, then `tendsto_const_nhds`.

## Build verification

`./proofs/scripts/docker-build.sh Proofs.CentralLimitTheoremOQ01OQ01OQ04` succeeded:
```
⚠ [7744/7744] Built Proofs.CentralLimitTheoremOQ01OQ01OQ04 (214s)
warning: Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean:100:29: unused variable `hn`
Build completed successfully (7744 jobs).
```

The one warning is pre-existing in `quadForm_scale_inv_sqrt` (line 100) and is unrelated to this session's change. No new errors or warnings introduced.

## State delta

| Field | Pre-S16 | Post-S16 |
|---|---|---|
| `axiomCount` | 3 | 2 |
| `theoremCount` (gallery meta) | 13 | 14 |
| `lineCount` | 447 | 493 |
| Remaining axioms | `operator_stable_linear_image`, `meerschaert_scheffler`, `finite_cov_in_gaussian_doa` | `operator_stable_linear_image`, `meerschaert_scheffler` |
| Vacuous-discharge bug-report theorems | 1 (`scalar_exponent_ge_half`) | 2 (`scalar_exponent_ge_half`, `finite_cov_in_gaussian_doa`) |

## Pattern observation (slug-wide)

Two of the three axioms standing post-S15 were vacuously dischargeable due to weak hypothesis bundles — S14 found this for `scalar_exponent_ge_half` (unsatisfiable `∀ v, P v → False`), and S16 finds it for `finite_cov_in_gaussian_doa` (missing finite-second-moment content + existential conclusion). The two remaining axioms (`operator_stable_linear_image`, `meerschaert_scheffler`) carry stronger statements that are *not* obviously vacuous and likely require genuine mathematical content to discharge.

This pattern is worth a gallery-wide audit: when an axiom carries a hypothesis bundle, check (a) whether the bundle is satisfiable, and (b) whether the bundle is sufficient for the *strong* claim or only for a vacuous existential. The S14+S16 combination strongly suggests the v4.26.0 axiomatization sweep produced hypothesis bundles that look plausible but do not carry the intended constraints. Other CLT-OQ slugs are candidates for the same check.

## S17 PREP picker (recommended)

**S17 PREP** — plan partial discharge of `operator_stable_linear_image` for the invertible-B subcase.

### Strategy outline

The current axiom:
```lean
axiom operator_stable_linear_image (d : ℕ) (φ : (Fin d → ℝ) → ℂ)
    (hφ : IsOperatorStable d φ) (B : Matrix (Fin d) (Fin d) ℝ) :
    IsOperatorStable d (fun ξ => φ (fun i => ∑ j, B i j * ξ j))
```

is too strong in the singular-B case (the image distribution can collapse to a lower-dimensional subspace where operator-stability holds only with a different `d`). For invertible B, the witness construction is:

1. Take the operator-stability witnesses `A_n, b_n` from `hφ`.
2. The new witnesses for `ξ ↦ φ(Bξ)` are `A_n B^T` (or `B^T A_n`, depending on convention) and `B^{-T} b_n`.
3. The verification reduces to a matrix-product identity: `((A_n B^T)^T ξ) = B (A_n^T ξ)`, which holds by `Matrix.transpose_mul` + associativity.

### Per-component effort estimate

- Invertible-B theorem statement + proof: ~40 LOC.
- Matrix-product manipulation lemmas (likely 1-2 small helpers): ~15 LOC.
- Renamed general-case axiom (singular B): ~5 LOC.
- Aggregate diff: ~60 LOC add, ~5 LOC del. Single Docker pass expected.

### Pre-PREP bearer audit (for S17)

Before pasting an S17 ACT:
- `Matrix.Invertible` typeclass + `Matrix.inv_mul_self`, `Matrix.mul_inv_self` are on the current pin.
- `Matrix.transpose_mul`, `Matrix.transpose_transpose` are present.
- `gaussian_is_operator_stable` (S11 ACT) as a use-case sanity check that the invertible-B theorem reproduces.

## Honest-status block

- **Mathematical progress**: 1 axiom→theorem promotion (`finite_cov_in_gaussian_doa`) via vacuous discharge. The discharge is honest about the hypothesis-bundle defect.
- **Build-verification status**: Docker 7744 jobs verified (214s), one pre-existing warning unchanged, no new warnings/errors.
- **Axiom status**: 3 → 2. Two vacuous-discharge bug-report theorems now flag hypothesis-bundle encoding issues.
- **Documentation accuracy**: gallery `meta.json` synced (axiomCount/lineCount/theoremCount/assumptions/originalContributions/leanFile block). Registry JSON synced (iteration 15 → 16, focus, nextAction, blockers, builtItems, insights, mathlibGaps, nextSteps, leanFiles[OQ04] block).
- **No saturation risk**: this is an ACT-class session (Lean code shipped), following S15 STATE-SYNC. Doc-only-saturation counter resets to 0.

## References

- **S13 ACT** (PR #22113, 2026-06-02) — `gaussian_in_own_doa` discharge; the recipe S15 picker recommended porting.
- **S14 ACT** (PR #22591, 2026-06-06) — `scalar_exponent_ge_half` vacuous discharge + bug report; the structural pattern S16 ACT extends.
- **S15 STATE-SYNC** (2026-06-10) — registry catch-up; identified S16 ACT as next move.
- **Mathematical** (for the *intended* strong statement, not discharged here): Meerschaert & Scheffler (2001), Theorem 7.1.1; Hudson & Mason (1981), "Operator-stable laws."
