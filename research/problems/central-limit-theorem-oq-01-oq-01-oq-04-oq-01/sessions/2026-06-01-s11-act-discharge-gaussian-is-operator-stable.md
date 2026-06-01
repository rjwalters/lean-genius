# S11 ACT — discharge `gaussian_is_operator_stable` (Docker-verified)

**Date**: 2026-06-01
**Researcher**: researcher-1
**Phase**: ACT
**Branch**: `research/clt-oq01oq01oq04oq01-s11-act-2026-06-01`
**Base commit**: `f486a19e2e0` (HEAD on `main`)
**Outcome**: axiomCount 6 → 5; theoremCount 10 → 11; lineCount 359 → 379; **Docker-verified 7744 jobs OK** (9.2s incremental)

## 1. Goal

Per S10 STATE-SYNC's Next Action list, S11 ACT replaces the axiom
`gaussian_is_operator_stable` at parent line 212 with a theorem, composing
`gaussian_has_scalar_exponent` (now a theorem, S9 ACT, PR #19652) with the
matrix witness `A_n = n^{-1/2} · I`.

## 2. Patch (parent file `Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean`)

Replace:

```lean
axiom gaussian_is_operator_stable (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    IsOperatorStable d (gaussCharFun d Sg)
```

with:

```lean
theorem gaussian_is_operator_stable (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    IsOperatorStable d (gaussCharFun d Sg) := by
  obtain ⟨b, hb⟩ := gaussian_has_scalar_exponent d Sg
  refine ⟨fun n => (n : ℝ) ^ (-(1 / 2 : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ),
          b, ?_⟩
  intro n hn ξ
  have h_arg :
      (fun i => ∑ j, ((n : ℝ) ^ (-(1 / 2 : ℝ)) •
        (1 : Matrix (Fin d) (Fin d) ℝ)) i j * ξ j)
        = (fun i => ξ i * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    funext i
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
               mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
               Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  rw [h_arg]
  exact hb n hn ξ
```

Plus an updated docstring noting the S11 ACT derivation.

## 3. Proof structure

`IsOperatorStable d φ` unfolds to:

```
∃ (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → Fin d → ℝ),
  ∀ n : ℕ, n ≠ 0 → ∀ ξ : Fin d → ℝ,
    (φ (fun i => ∑ j, A n i j * ξ j)) ^ n
      = φ ξ * exp (I * (vecInner d (b n) ξ : ℝ))
```

`HasScalarExponent d φ c` unfolds to the same shape but with the LHS taking
`fun i => ξ i * n^(-c)` instead of `fun i => ∑ j, A n i j * ξ j`.

Plan: pick `A_n = n^(-1/2) • (1 : Matrix _ _ _)` (scalar diagonal matrix).
Then `∑ j, A_n i j * ξ j = n^(-1/2) * ξ i = ξ i * n^(-1/2)`, matching the
LHS of `gaussian_has_scalar_exponent d Sg : HasScalarExponent d _ (1/2)`.
Take `b` from that existential and the goal closes by `exact hb n hn ξ`.

The `h_arg` step does the matrix→scalar reduction:
- `Matrix.smul_apply` rewrites `((n^(-1/2)) • 1) i j = n^(-1/2) • (1 i j)`
  = `n^(-1/2) * (1 i j)` (via `smul_eq_mul` on ℝ).
- `Matrix.one_apply` rewrites `(1 : Matrix _ _ _) i j = if i = j then 1 else 0`.
- After distributing the multiplication through the if (`mul_ite`/`ite_mul`),
  the sum is `∑ j, if i = j then n^(-1/2) * ξ j else 0`.
- `Finset.sum_ite_eq` collapses it to `n^(-1/2) * ξ i` (membership trivial
  on `Finset.univ`).
- `ring` finishes the `n^(-1/2) * ξ i = ξ i * n^(-1/2)` flip.

## 4. Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.CentralLimitTheoremOQ01OQ01OQ04
...
⚠ [7744/7744] Built Proofs.CentralLimitTheoremOQ01OQ01OQ04 (9.2s)
warning: Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean:100:29: unused variable `hn`
warning: Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean:249:40: This simp argument is unused: Pi.zero_apply
warning: Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean:373:17: unused variable `hφ_reg`
Build completed successfully (7744 jobs).
=== Build succeeded ===
```

Exit code 0. All 3 warnings pre-date this PR (line 100 = `gaussCharFun_zero`,
line 249 = `univariate_embed_stable`, line 373 = `finite_cov_in_gaussian_doa`
axiom signature). No new warnings introduced by S11.

## 5. File metrics

| Metric | Pre-S11 | Post-S11 | Δ |
|--------|---------|----------|---|
| lineCount | 359 | 379 | +20 |
| axiomCount | 6 | 5 | −1 |
| theoremCount | 10 | 11 | +1 |
| definitionCount | 7 | 7 | 0 |
| sorries | 0 | 0 | 0 |

Remaining 5 axioms (all KEEP, see S10 STATE-SYNC):
- `operator_stable_linear_image` (line 272 → +20 = 292)
- `scalar_exponent_ge_half` (line 302 → 322)
- `meerschaert_scheffler` (line 317 → 337)
- `gaussian_in_own_doa` (line 341 → 361)
- `finite_cov_in_gaussian_doa` (line 349 → 369)

## 6. Bearer table

All bearers used in the S11 patch are on the existing import chain
(`import Mathlib`); no new imports required. Pin-verified at lake-manifest
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0):

| API | File | Line | Note |
|-----|------|------|------|
| `Matrix.smul_apply` | `LinearAlgebra/Matrix/Defs.lean:224` | 224 | `@[simp]` |
| `Matrix.one_apply` | `Data/Matrix/Diagonal.lean:212` | 212 | — |
| `Finset.sum_ite_eq` | `Algebra/BigOperators/Group/Finset/Piecewise.lean` | (via `to_additive`) | from `Finset.prod_ite_eq` |
| `smul_eq_mul` | core | — | Module ℝ instance |
| `gaussian_has_scalar_exponent` | this file:186 | 186 | proved in S9 ACT |

## 7. Gallery `meta.json` updates

Both `meta.axiomCount`/`meta.lineCount`/`meta.theoremCount` and
`leanFile.axiomCount`/`leanFile.lineCount`/`leanFile.theoremCount` updated
in `src/data/proofs/central-limit-theorem-oq-01-oq-01-oq-04/meta.json`:

- axiomCount: 6 → 5
- lineCount: 359 → 379
- theoremCount: 10 → 11
- assumptions: dropped `gaussian_is_operator_stable` from the pending list
  (moved into the "discharged" parenthetical alongside `gaussCharFun_norm_le_one`
  and `gaussian_has_scalar_exponent`).
- originalContributions: added bullet for `gaussian_is_operator_stable`.

## 8. Sibling-coordination

`gh pr list --search "central-limit-theorem-oq-01-oq-01-oq-04 is:open"`
returns 0 open PRs at S11 ACT push time. No race risk.

## 9. Risk inventory

All RED items from S10 STATE-SYNC drained:
- **R-INFRA-Docker**: drained — Docker daemon GREEN (29.4.1 server responsive
  at S11 build time).
- **R-INFRA-disk**: drained — 55 Gi avail (was 5.4 Gi at S10).
- **R-INFRA-lake-self-loop**: empirically inert under Docker (`-v` mount
  overrides; same as the parallel S3 ACT on sperner-mathlib-oq-01 confirmed
  this 2026-06-01).

## 10. S12+ readiness (S11 → S12 handoff)

`gaussian_in_own_doa` at post-S11 parent line 361 is the next discharge
target. Per S4 PREP §4.6 sketch, it should be ~25-40 LOC composing the
existing `gaussian_in_own_doa_via_charfun_form` companion (line ~ check
when claimed). Independent of S11 — S12 can be ACTed without further
prerequisites.

After S12 lands, only KEEP-axiomatized assumptions remain (4 → 3 trajectory
needs gaussian_in_own_doa → out → axiomCount 5 → 4).

## 11. Decisions log

- **Witness `A_n = n^{-1/2} • 1`**: scalar-matrix form chosen over
  `Matrix.diagonal (fun _ => n^{-1/2})`. Both give the same matrix; `• 1`
  is shorter and the bridge to `gaussian_has_scalar_exponent` is cleaner
  (`Matrix.smul_apply` + `Matrix.one_apply` are both `@[simp]`).
- **`Finset.sum_ite_eq` vs `Finset.sum_ite_eq'`**: chose unprimed because
  `Matrix.one_apply` produces `if i = j then 1 else 0` with `i` (the outer
  binder) first; the unprimed `sum_ite_eq` matches `ite (a = x)` with
  bound `x`, which corresponds to `i = j` with bound `j`.
- **`ring` after `simp only`**: simp leaves `n^{-1/2} * ξ i`; the goal
  is `ξ i * n^{-1/2}`. `ring` handles the commutation, more robust than
  a hand-crafted `mul_comm`.
- **Drift `b` taken from `hb`**: rather than supplying `fun _ => 0`
  explicitly, the proof reuses whatever drift witness `gaussian_has_scalar_exponent`
  provides (its proof picks `fun _ => 0`, but the abstraction doesn't
  require us to know that).

## 12. LOC budget

Net +20 LOC. The pre-S11 axiom + docstring was 9 LOC; the post-S11 theorem
+ updated docstring is 29 LOC. The parent file is now 379 LOC total.
Acceptable: the axiom discharge unblocks downstream gallery status
improvements (axiomCount 6 → 5 moves the slug strictly closer to the
4-axiom KEEP floor).
