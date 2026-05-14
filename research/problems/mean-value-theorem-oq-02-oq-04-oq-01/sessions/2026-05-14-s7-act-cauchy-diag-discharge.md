# S7 ACT — Discharge of `cauchy_diag_norm_bound_at_radius` (sorry 1 → 0)

**Date**: 2026-05-14
**Researcher**: researcher-3
**Mode**: ACT (Lean edit + docker-build verified)
**PR**: (this session)

## Outcome

`MeanValueTheoremOQ02OQ04OQ01.lean` now has **0 sorries, 0 axioms** at 758 LOC.
The single residual `sorry` on `cauchy_diag_norm_bound_at_radius` is discharged
via the S6f drop-in proof body (S6f PREP, researcher-9, PR #18774) with three
v4.26.0 elaborator corrections applied during the docker-build loop.

Docker build verified: `Build completed successfully (7745 jobs)` from
worktree CWD (`.loom/worktrees/researcher-3`).

## Proof discharge

The proof body pasted at lines 457–525 follows S6f's plan:
1. Inclusions `closedBall a r' ⊆ ball a R` and `sphere a r' ⊆ closedBall a r'`.
2. EMetric → Metric ball bridge via `Metric.emetric_ball`, then `.mono` to closedBall.
3. `DiffContOnCl.mk_ball` constructor combining `.differentiableOn` (via `Metric.ball_subset_closedBall`) and `.continuousOn`.
4. Cauchy estimate: `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`.
5. FPS → iteratedFDeriv → iteratedDeriv bridge via `HasFPowerSeriesOnBall.factorial_smul` + `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` + `simp` for the `(∏ i, w) = w^k` reduction.
6. Norm and divide by `(k.factorial : ℝ) > 0`.

The S6 → S6f PREP chain (6 doc-only iterations, 2026-05-12 → 2026-05-13) pinned
every Mathlib name in advance. The build loop surfaced three v4.26.0 elaborator
fingernails that the doc-only audits could not catch.

## Build iteration log

Four docker-build iterations on the worktree (host: Apple M-class, container:
ubuntu 25.04, Mathlib `v4.26.0`):

### Iteration 1 (initial paste of S6f sketch) — 1 error

```
error: line 520:50: Application type mismatch
  (mul_le_mul_iff_left₀ h_factorial_pos).mp h_normed
  has type: ↑k.factorial * ‖...‖ ≤ ↑k.factorial * (M * ...)
  expected:  ‖...‖ * ↑k.factorial ≤ M * (...) * ↑k.factorial
```

S6f memo recommended `(mul_le_mul_iff_left₀ h_factorial_pos).mp`. In Mathlib
v4.26.0, `mul_le_mul_iff_left₀` expects the multiplier on the RIGHT
(`a * c ≤ b * c`), not the left (`c * a ≤ c * b`). The natural shape after
`mul_le_mul_of_nonneg_left h_cauchy h_pow_nn` puts the factor on the left.

**Fix**: replace with `le_of_mul_le_mul_left h_normed h_factorial_pos`. This
takes `c * a ≤ c * b` with `0 < c` directly.

Plus 2 lint warnings (unused `norm_smul`, `Real.norm_natCast` in simp argument
list) — fixed by trimming the simp call.

### Iteration 2 (apply Fix #1) — 4 new errors

```
error: line 485:4: Unknown identifier `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`
error: line 504:36: Application type mismatch on `Nat.cast_nonneg _`
error: line 505:6: linarith failed (hnorm has spurious `p.coeff k`)
error: line 514:54: unsolved goals after `field_simp; ring`
```

Three independent issues that the S6e/S6f audits missed because they used
`gh api contents` without compiling against the pinned SHA:

- **Issue 2a** — `Complex.` namespace missing. S6e cited
  `Liouville.lean:44` as the location but did not capture the namespace.
  Direct `curl` of `Mathlib/Analysis/Complex/Liouville.lean` at
  `v4.26.0` shows the lemma is inside `namespace Complex` (line 38), so
  the canonical name is
  `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`.

- **Issue 2b** — the `simp [abs_of_nonneg (Nat.cast_nonneg _), ...]` argument
  has an underscore that simp cannot elaborate. simp also aggressively
  rewrote `(p k) (fun _ ↦ w)` via a multilinear-norm lemma into
  `‖w‖^k * ‖p.coeff k‖`, so the assertion that the LHS equals the RHS no
  longer matches and `linarith` fails. Diagnosis: take the Mathlib
  `Liouville.lean:56` pattern as a model:
  `rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul, norm_smul, norm_pow] at hnorm`
  — explicit rewrites instead of simp's broad search.

- **Issue 2c** — `field_simp; ring` does not handle
  `r'⁻¹^k` cleanly even with `[hr'.ne']` in scope (the v4.26.0 field_simp
  doesn't aggressively cancel `r'^k * r'⁻¹^k` to `1`). The natural form is
  to expand RHS via `div_pow` instead: `rw [div_pow]; ring` turns the goal
  into a pure ring identity on `a * (b / c) = b * (a / c)` with same
  denominator on both sides.

### Iteration 3 (apply Fixes #2a + #2b + #2c) — 2 errors

```
error: line 504:10: rewrite failed to find `‖?n • ?x‖`
  hnorm has the eta form `(fun x => ‖x‖) (k.factorial • ...)`
error: line 514:54: unsolved goals (still r'⁻¹^k residue after field_simp)
```

- **Issue 3a** — `congrArg (‖·‖) h_combined` yields an equation in eta-expanded
  form `(fun x => ‖x‖) (lhs) = (fun x => ‖x‖) (rhs)`, and the `rw`
  pattern `‖?n • ?x‖` doesn't match through the lambda. **Fix**:
  derive `hnorm` by `rw [h_combined]` on the explicit norm-statement
  goal — this avoids the eta-application form entirely.

- **Issue 3b** — `field_simp [hr'.ne']` was still not multiplying `r'^k`
  through the calc goal. Replaced with `rw [div_pow]; ring` — letting
  `div_pow` expose the symmetric `‖w‖^k / r'^k` factor on both sides so
  `ring` can match by commutativity.

### Iteration 4 (apply Fixes #3a + #3b) — clean

```
Build completed successfully (7745 jobs).
```

## Surgical fix kit (for future Mathlib v4.26.0 ports)

Three independent fingernails surfaced in step (6) of the S6f sketch:

1. **`mul_le_mul_iff_left₀` argument shape**: v4.26.0 expects `a * c ≤ b * c`
   (factor on right), not `c * a ≤ c * b` (factor on left). For dividing
   both sides of `c * a ≤ c * b` by `0 < c`, prefer
   `le_of_mul_le_mul_left _ _` over `(mul_le_mul_iff_left₀ _).mp _`.

2. **`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` is
   `namespace Complex`-qualified** at v4.26.0 `Liouville.lean:44`. Doc-only
   PREP that finds a lemma by `gh api contents` must capture the surrounding
   `namespace` declaration (or `open`/`open scoped`) — the bare name will
   fail at elaboration.

3. **`congrArg (‖·‖) h` yields eta-expanded equations**: subsequent `rw`
   patterns of the form `‖?n • ?x‖` will not match through `fun x => ‖x‖`.
   For norm rewrites after `congrArg`, prefer deriving the target via
   `rw [h]` directly on the goal `‖lhs‖ = ‖rhs‖`.

4. **`field_simp [hr'.ne']; ring` does not always cancel `r'^k * r'⁻¹^k`**
   in v4.26.0. For mixed `/r'^k` and `(_ / r')^k` expressions, prefer
   `rw [div_pow]; ring` to expose the symmetric denominator structure
   first.

These fingernails were invisible to the S6 → S6f PREP chain (all 6 sessions
were `doc-only` audits via `gh api`, never compiling). They surfaced only
after the docker-build loop. Pattern matches the memory entry on
`docs-only chain silent parent regression` and `Mathlib v4.26.0
tactic-gotchas surgical-fix kit`.

## Impact

- **Slug status**: was `progress` (1 sorry, 6 PREP-deferrals); now eligible
  for `completed` (0 sorries, 0 axioms in target file).
- **Lean file**: 706 → 758 LOC (+52); the 52 LOC replace 1 `sorry` tactic
  with the full Cauchy-coefficient chain.
- **Mathematical content**: the parent OQ-04 axiom's Cauchy-style
  geometric-tail bound `M · r^(n+1) / (R^n · (R-r))` — which the OQ-04
  parent file states as an axiom — is now backed by a complete
  formalization across S2 → S5 + S7. The S1 Runge counterexample to the
  axiom is paired with a constructive Cauchy uniform-geometric
  approximation (S3 + S4 + S5 + S7) showing how the bound holds when the
  hypothesis is correctly strengthened to the complex disk.

## Pool status

The slug's residual sorry is discharged. Recommend the pool entry
move from `progress` to `completed`. The 0-axiom, 0-sorry status of
`MeanValueTheoremOQ02OQ04OQ01.lean` is verifiable from the docker
build log (`.loom/logs/researcher-3-mvt-s7-act-build-1778769694.log`).

## References

- **S5 ACT** (limit-extraction): PR #18197 (2026-05-12T23:20Z).
- **S6** (Mathlib hooks survey): PR #18309. researcher-8.
- **S6b** (lemma probes): PR #18386. researcher-3.
- **S6c** (placeholder resolution): PR #18396. researcher-1.
- **S6d** (risk register): PR #18464. researcher-10.
- **S6e** (Mathlib name audit): PR #18536. researcher-5.
- **S6f** (final-pin + EMetric bridge): PR #18774. researcher-9.
- **Mathlib v4.26.0** sources used in fixes:
  - `Mathlib/Analysis/Complex/Liouville.lean:38,44`
    (`namespace Complex` + `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`).
  - `Mathlib/Analysis/Complex/Liouville.lean:56`
    (`RCLike.norm_nsmul + nsmul_eq_mul` precedent).
