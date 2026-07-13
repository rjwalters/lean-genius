# S6d PREP — S7 ACT pre-flight risk register (doc-only)

**Author:** researcher-10
**Timestamp:** 2026-05-13 ~03:00 UTC
**Phase:** S6d PREP (refinement of S6c — final pre-flight before S7 ACT)
**Iteration:** 13 (post-S6c PREP, by researcher-1)
**Builds on:**
- S5 ACT — researcher-? PR #18197 (merged, limit-extraction proof)
- S6 PREP — researcher-8 PR #18309 (merged, Mathlib drift survey)
- S6b PREP — PR #18386 (merged, lemma-name probe + proof outline)
- S6c PREP — researcher-1 PR (merged, placeholder resolution for P1/P2/P3)

## Purpose

After S6b's lemma-name table + S6c's placeholder resolutions, the
single residual sorry on `cauchy_diag_norm_bound_at_radius` has a
**complete static proof script**. This S6d PREP is a **risk register
for the S7 ACT** — what gotchas / drift items / cross-step gaps will the
next researcher hit when actually pasting the assembled script into the
file and running the docker build.

Doc-only — pristine `sessions/2026-05-13-s6d-prep-s7-act-risk-register.md`.
No edits to `problem.md`, `state.md`, `knowledge.md`, gallery JSON, or
any Lean file. Conflict-free against open PR #17904 (obsolete S2 ACT).

## R-1 — `Complex.norm_natCast` vs `Complex.abs_natCast` naming

**S6c §3 resolution** writes:

```lean
rw [norm_smul, norm_smul, norm_pow, Complex.norm_natCast] at h_normed
```

**Risk.** At v4.26.0, the canonical name for `∀ n : ℕ, ‖(n : ℂ)‖ = n`
may be `Complex.norm_natCast` OR `Complex.abs_natCast` OR neither (an
`@[simp]` lemma that requires `simp`-driven rewriting rather than
named `rw`). The file's existing line 593-595 (S2 proof) **uses
`Complex.abs_natCast`** explicitly:

```lean
-- file line 593-595 (verified working):
simp only [Complex.abs_natCast, Nat.cast_id, ...]
```

This is a one-of `norm` vs `abs` divergence — in Mathlib v4.26.0, on
`ℂ`, `‖z‖ = Complex.abs z` as a defeq, but `Complex.abs_natCast` is
the named form and `Complex.norm_natCast` is conjecturally an alias.

**Mitigation.** Pre-test the S6c §3 chain with `Complex.abs_natCast`
as primary, `Complex.norm_natCast` as fallback. The file's S2 pattern
at line 593-595 gives the working precedent.

If both fail, the third fallback is `show (k.factorial : ℂ) = (k.factorial : ℝ)`
which is just the natural cast and `norm_cast` discharges.

## R-2 — `EMetric.ball` vs `Metric.emetric_ball`

**S6c §2 alternative form** suggests:

```lean
-- Alternative: Metric.closedBall_subset_ball + emetric_ball_nnreal coercion
```

**Risk.** Mathlib v4.26.0 has both `EMetric.ball` (the primary EMetric
formulation) and various `Metric.emetric_ball*` coercion lemmas. The
exact spelling for converting `Metric.ball a R ⊂ EMetric.ball a (ENNReal.ofReal R)`
varies — at least three candidates exist:

- `Metric.emetric_ball_nnreal`
- `Metric.ball_eq_ball` (if available)
- Direct `ENNReal.ofReal_lt_ofReal_iff_of_nonneg` rewrite (S6c §2 primary)

**Mitigation.** S6c §2 already provides the direct-rewrite primary
form (5 lines), citing the in-file precedent at lines 582-584 (S2's
own EMetric.ball conversion). Use the primary form. The "alternative"
should only be tried if the primary form breaks (e.g. due to a
v4.26.0-specific `EMetric` API revamp), at which point the in-file
precedent must also be broken, signalling a wider drift.

## R-3 — `Filter.Tendsto.le_of_tendsto` direction-of-inequality

**S5 ACT** (PR #18197, merged) uses `le_of_tendsto` to lift an
eventual `≤` bound to a limit bound. The S7 ACT inherits this — it
does NOT re-do the limit step (S5 already proved
`cauchy_diag_norm_bound` from `cauchy_diag_norm_bound_at_radius`).

**Risk.** None on S7 ACT itself. But: if a future iteration tries to
swap `cauchy_diag_norm_bound` / `cauchy_diag_norm_bound_at_radius`
roles (e.g. shift the residual sorry to the boundary form), the
direction matters. `Filter.Tendsto.le_of_tendsto` requires the bound
sequence to be on the *upper* side; for an eventual `lo ≤ f r'`
bound, use `ge_of_tendsto` (or rewrite via `not_lt`).

**Mitigation.** Don't touch S5's already-proven structure. The S7 ACT
fills in `cauchy_diag_norm_bound_at_radius` only; the limit step is
S5's domain. (Confirmed by `state.md` § "Iteration 5".)

## R-4 — `iteratedFDeriv k f a` vs `iteratedDeriv k f a` (real vs complex iterated derivative)

**S6 PREP §3 step (b)** uses
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` —
operating on **`iteratedDeriv`** (single-variable, scalar) NOT on
**`iteratedFDeriv`** (multivariable, multilinear).

**Risk.** The bridge ★ identified by S6 PREP
(`HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace`)
operates on **`iteratedFDeriv`**. To stitch (b) and (c), the proof
must convert:

```
‖iteratedDeriv k f a‖ ≤ k! · M / (r')^k       -- Cauchy bound (b)
                                                ↓
                                          [needs conversion]
                                                ↓
‖iteratedFDeriv k f a (Λ_w)‖ ≤ ‖w‖^k · ‖iteratedDeriv k f a‖    -- (b → c)
```

where `Λ_w = (w, w, ..., w)` is the diagonal multilinear input.

The conversion uses `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`
(S5 PR docstring #8) — or equivalent. At v4.26.0, the precise name
may be `iteratedFDeriv_apply_eq_iteratedDeriv_mul_pow` or
`iteratedFDeriv_one_apply` (single-variable specialization).

**Mitigation.** This is a **net-new lemma** the S7 ACT must invoke.
Pre-flight: `gh api search/code 'q="iteratedFDeriv_apply" "iteratedDeriv" repo:leanprover-community/mathlib4'`
should give the canonical name at v4.26.0. If still ambiguous, fall
back to the file's own `Complex.differentiableAt_iff_hasDerivAt`
pattern (line 581-630) to manually compute the iterated derivative.

**Estimated cost if drift hits:** 5-15 extra LOC.

## R-5 — `Complex.norm_real_complex` is a phantom name (S6c flagged)

**S6c §3 P3 resolution** notes:

> `Complex.norm_real_complex` ❌ does not exist — replace with
> `Complex.norm_real` or use the identity-via-`norm_smul` chain.

**Risk.** Low — S6c already resolved by routing through `norm_smul`
+ `norm_pow` + `Complex.norm_natCast`, eliminating the dependency on
`Complex.norm_real_complex` entirely.

**Mitigation.** None needed (already resolved by S6c).

## R-6 — `_hf` (unused-hypothesis) marking changing post-merge

The current sorry signature has `_hf` and `_hbound` marked as unused
(`_` prefix). The S7 ACT will use them, so the **rename**:

```lean
theorem cauchy_diag_norm_bound_at_radius
    (f : ℂ → ℂ) (a : ℂ) (R M : ℝ)
    (_hR : 0 < R) (_hM : 0 ≤ M)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (_hf : HasFPowerSeriesOnBall f p a (ENNReal.ofReal R))      -- needs rename: hf
    (_hbound : ∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M)                -- needs rename: hbound
    (k : ℕ) (w : ℂ) (r' : ℝ) (_hr' : 0 < r') (_hr'R : r' < R) : -- needs rename: hr', hr'R
    ‖p k (fun _ ↦ w)‖ ≤ M * (‖w‖ / r') ^ k
```

**Risk.** Forgetting to drop the underscore prefix on hypotheses
used by the proof body. Lean 4 doesn't complain about
named-but-underscore-prefixed hypotheses being used (the underscore
is just a style convention for "unused"), but `set_option
linter.unusedVariables true` may warn. **The file already has
`set_option linter.unusedVariables false`** at line 124 (verify),
so no actual error — just a style nit.

**Mitigation.** Either (a) drop underscores on all four hypotheses
used by the new proof, OR (b) keep underscores and rely on the
disabled linter. Recommended: drop underscores for readability.

## R-7 — Build time + .lake symlink loop

**Risk.** Per project memory
`feedback_researcher_lake_symlink_loop_and_wipe.md`: docker build
takes 25-45 min, the worktree's `.lake` symlink may be self-referential,
and the daemon's 30-min respawn threshold can wipe uncommitted work
mid-build.

**Mitigation.** S7 ACT MUST:
1. Commit + push the Lean file change FIRST (before `docker-build.sh`).
2. Open PR as "build pending" with explicit title.
3. Let Doctor pick up build verification from a clean worktree.

This is the same pattern as the S5/S6 PRs in this slug's history.

## R-8 — Cross-step variable-name consistency

S6b §3 + S6c collectively use these variable names: `M`, `f`, `a`,
`R`, `r'`, `p`, `k`, `w`, `z`, `hbound`, `hf`, `hr'`, `hr'R`,
`h_combine`, `h_normed`, `h_norm`, `h_sphere_bound`, `hz`, `hz_eball`,
`h_iteratedFDeriv_bridge`, `h_cauchy_bound`, `h_diag_collapse`,
`h_factor_smul`, `hf_diff_closedBall`.

**Risk.** Inconsistencies between S6b and S6c (e.g. S6b uses `hbound`
while S6c §1 uses `hbound`, both consistent; but S6c §2 introduces
`hf_diff_closedBall`, not previously named in S6b).

**Mitigation.** S6d (this doc) makes the variable-name table
explicit. S7 ACT should walk through S6b §3 + S6c §1 + S6c §2 + S6c §3
in sequence, ensuring each `have h_X` introduction matches the next
step's consumer. The line-by-line audit takes ~15 minutes.

## R-9 — `FormalMultilinearSeries.norm_apply_le` direction

The **target conclusion** is `‖p k (fun _ ↦ w)‖ ≤ M * (‖w‖ / r')^k`.

After applying the bridge ★ to convert `p k` to
`iteratedFDeriv k f a / k!` and using the Cauchy bound on
`iteratedDeriv`, the resulting RHS is:

```
(k.factorial : ℝ) * ‖p k (fun _ ↦ w)‖
  ≤ (k.factorial : ℝ) * M * (‖w‖ / r')^k         -- ÷ k.factorial both sides
```

The divide-by-`k.factorial` step requires `(k.factorial : ℝ) > 0`,
which is immediate from `Nat.factorial_pos`. But the
`le_div_iff_mul_le` (or `div_le_iff`) direction must be carefully
chosen — `le_div_iff_pos.mpr` vs `le_div_iff_neg.mpr`.

**Mitigation.** Use:
```lean
exact (le_div_iff (Nat.cast_pos.mpr k.factorial_pos)).mp h_intermediate
```

Cite the in-file precedent if exists. Worst case, `field_simp` over
`Nat.factorial_pos` and direct linarith / nlinarith / positivity.

## R-10 — Final integration risk: build heart-attack

The S7 ACT proof body is now ~50-80 LOC (S6b's steps (a)+(b)+(c) +
S6c's three resolutions + the divide-by-factorial finisher). With
~10 distinct Mathlib lemma invocations, each is a potential drift
point.

**Mitigation.**
1. **Stage commit each substep** — if step (a) builds but (b) breaks,
   the residual sorry shifts cleanly to (b)'s output.
2. **Use `show` aggressively** — after each `have h_X : ... := ...`,
   `show` the next goal explicitly so the build error message points
   to the exact line.
3. **Keep `sorry` placeholders ladder-style** — if (c.iv) breaks,
   leave it `sorry`, push, let Doctor diagnose.

This is the "fail-fast at the smallest substep" strategy that worked
for S5 (PR #18197, build verified).

## Anti-targets (this S6d PREP explicitly does NOT do)

1. **Does not modify any Lean file.** Pre-flight risk register only.
2. **Does not produce a single integrated proof script.** S6b §3 +
   S6c §1-§3 collectively give the proof; S6d audits the integration
   risks, not the proof content.
3. **Does not run docker build.** Static audit only.
4. **Does not propose new Mathlib lemmas.** All Mathlib references
   come from S6, S6b, S6c (re-cited here for completeness).
5. **Does not modify `state.md` / `problem.md` / `knowledge.md` /
   `meta.json` / gallery JSON.** Pristine, single new `sessions/`
   file.

## Race awareness

Pre-push checks (2026-05-13 ~03:05 UTC):

- `gh pr list --search "mean-value-theorem-oq-02-oq-04-oq-01 in:title"`
  returns 1 PR (#17904, obsolete S2 ACT). Zero overlap with this
  doc-only PR's diff.
- 9 merged PRs on the slug (S1-S6c).
- No active Doctor / Mechanic branches.

## Honesty / what could be wrong

- I have NOT run docker build. All claims are static-audit grade.
- The R-1 (`Complex.norm_natCast` vs `Complex.abs_natCast`) risk is my
  read — I did not re-verify the v4.26.0 name. S6c's recommended
  `Complex.norm_natCast` may actually be canonical and `abs_natCast`
  the alias.
- The R-4 (iteratedFDeriv ↔ iteratedDeriv conversion) is the biggest
  net-new step the S7 ACT needs. The S5/S6/S6b/S6c PREPs do not
  fully resolve it — they cite the candidate name
  `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` but do not pin a
  v4.26.0 location. S7 ACT must do this lookup as part of the work.
- The R-10 substep-staging strategy is project-folklore (per S5 PR
  #18197's success); not formally documented. Real-world build
  timing may vary.

## Next iteration after this PREP

S7 ACT — pick up S6b + S6c + this S6d, paste assembled proof into
`MeanValueTheoremOQ02OQ04OQ01.lean`, attempt docker build.

**Expected outcome:** sorry count 1 → 0. Build status: if all 10
risks above are correctly anticipated, build passes; otherwise
escalate to Doctor with the specific failing substep marked.

**Estimated S7 ACT LOC:** ~50-80 LOC (replacing the single sorry).
File grows 705 → ~785 lines.

## Future status

This slug, once the build passes, will be **`verified`** (0 axioms,
0 sorries, all proofs against Mathlib v4.26.0). The seeker's OQ-04
target — a Cauchy-style estimate with explicit constants — is then
complete.

The slug's main contribution is **negative**: refuting the parent's
OQ-04 axiom via Runge's counterexample (`runge y = 1/(1+y²)` — S1).
The positive contribution is the **corrected uniform-geometric
approximation** (S2-S6) — replacing the parent's overstrong form
with a Mathlib-compatible (`HasFPowerSeriesOnBall.uniform_geometric_approx'`)
existential.
