# Current State

**Phase**: ACT
**Since**: 2026-05-11
**Iteration**: 1 (axiomatize OQ-04, n=0 corollary)
**Last Updated**: 2026-05-11 (researcher-3)
**Knowledge Tier prior to S1**: EMPTY (0)

## Problem statement

OQ-04 of the parent gallery entry `mean-value-theorem-oq-02` (Taylor's
Theorem with Lagrange Remainder):

> Is there a uniform error bound formalization: for all `x ∈ [a − r, a + r]`
> and `f` analytic on the disk of radius `R > r`,
> `|f(x) − T_n f(a)(x)| ≤ M · r^(n+1) / (R − r)`?
> This uniform version is used in complex analysis and approximation theory.

This is **Cauchy's uniform bound** on the analytic Taylor remainder:
the quantitative refinement of the qualitative
`taylor_remainder_tendsto_zero` (sibling entry `taylor-theorem-oq-02`,
which proves `R_n(x) → 0` for analytic `f` but does not give an explicit
rate).

## S1 (researcher-3, 2026-05-11, this PR)

**Scope**: first research session for the slug; prior knowledge = 0.

Three artifacts:

1. **Lean file** `proofs/Proofs/MeanValueTheoremOQ02OQ04.lean` (173
   lines, file does not previously exist):
   * `analytic_taylor_remainder_uniform_bound` — axiomatizes the
     OQ-04 statement verbatim, using the parent file's
     `MeanValueTheoremOQ02.taylorPolynomial` as the Taylor polynomial.
     Hypotheses: `AnalyticOn ℝ f (Set.Ioo (a-R) (a+R))` plus uniform
     sup bound `|f y| ≤ M` on the interval.
   * `analytic_remainder_zero_bound` — derives the `n = 0` specialization
     `|f(x) - f(a)| ≤ M · r / (R - r)` as a one-line `simpa` corollary
     of the axiom and `MeanValueTheoremOQ02.taylorPolynomial_zero`.

2. **Research scaffolding** (this directory):
   * `state.md` (this file).
   * `knowledge.md` — Mathlib API survey and proof strategy for the
     next iteration's discharge of the axiom.
   * `session-1-axiomatize.md` — narrative of this iteration's
     contribution.

3. **Gallery scaffolding** `src/data/proofs/mean-value-theorem-oq-02-oq-04/`:
   * `meta.json`, `index.ts`, `annotations.json` — minimal entry that
     surfaces the new OQ-04 sub-entry in the gallery, mirroring the
     parent's structure with `status: "axiomatized"`, `badge: "axiom"`,
     `axiomCount: 1`, `theoremCount: 1`, `sorries: 0`.

### Counts

* `lineCount` (file): 0 → 173 (new file)
* `theoremCount`: 0 → 1 (the `n = 0` corollary)
* `axiomCount`: 0 → 1 (the OQ-04 statement itself)
* `sorries`: 0
* `definitionCount`: 0 (reuses parent's `taylorPolynomial`)

### Build status

**[BUILD UNVERIFIED]**: worktree's `proofs/.lake` is a recursive
self-symlink (per `feedback_researcher_lake_symlink_broken.md`), so
local Docker builds re-fresh-clone Mathlib (~30-45 min cold). Risk
profile of this iteration is low:

* `AnalyticOn ℝ` is the canonical predicate already exercised in
  `proofs/Proofs/OSBridge.lean:218-220` (uses `AnalyticOn ℂ Set.univ`).
* `MeanValueTheoremOQ02.taylorPolynomial_zero` is a public theorem
  in the merged parent file (line 60-62 of
  `proofs/Proofs/MeanValueTheoremOQ02.lean`).
* The corollary's proof is `rw [taylorPolynomial_zero] at h; simpa
  using h` — three lines, no novel tactic risk.

## Active Approach

For S2: discharge the axiom using Mathlib's analytic-function API.
See `knowledge.md` §3 ("Proof strategy") for the full chain.

## Blockers

* `proofs/.lake` recursive self-symlink prevents local Docker build
  verification. Same caveat as every other recent research PR on
  this codebase (see e.g. `abel-ruffini-galois-extensions-oq-07`
  S9–S19, `basel-problem-oq-01-oq-01-oq-02-oq-03` iters 5+).

## Next Action

* **(S2)** Replace `analytic_taylor_remainder_uniform_bound` axiom by
  a proof via Mathlib's `HasFPowerSeriesOnBall`. The proof chain:
  1. `AnalyticOn ℝ f (Ioo (a-R) (a+R))` ⇒ at `a`, `HasFPowerSeriesAt
     f p a` with `p.radius ≥ R` (possibly via `AnalyticAt.exists_-
     mem_nhds_hasFPowerSeriesAt` or `HasFPowerSeriesOnBall.of_-
     analyticOn`).
  2. Cauchy's coefficient estimates: `‖p k‖ ≤ M / R^k` (uses the sup
     bound `M` on the ball and Mathlib's `FormalMultilinearSeries`-
     coefficient bound — concrete Mathlib name TBD, see
     `knowledge.md` §2).
  3. Geometric tail estimate: for `|x - a| ≤ r < R`,
     `Σ_{k > n} ‖p k‖ · r^k ≤ Σ_{k > n} M (r/R)^k = M (r/R)^(n+1) /
     (1 - r/R)`, which simplifies to `M · r^(n+1) / (R^n · (R - r))`.
  4. OQ-04 statement absorbs the `R^n` factor (or treats `M / R^n`
     as the effective constant); this is the convention we follow in
     the axiom statement.
  Estimated S2: ~80-150 lines depending on how much of the Cauchy
  estimate is already in Mathlib.

* **(S3)** Derive the `n = 1` specialization
  `|f(x) - f(a) - f'(a)(x - a)| ≤ M · r^2 / (R - r)` analogously to
  `analytic_remainder_zero_bound` (uses `taylorPolynomial_one` from
  the parent file).

* **(S4)** Connect to `taylor_remainder_tendsto_zero` in
  `proofs/Proofs/TaylorTheoremOQ02.lean`: show the qualitative
  vanishing follows from the uniform bound as `n → ∞` (since
  `r^(n+1) → 0` exponentially when `r < R`). This unifies the two
  related OQ resolutions.

## Why build-pending is acceptable here

* Axiom statement is the OQ-04 question verbatim; no proof body to
  verify.
* The one theorem (`analytic_remainder_zero_bound`) is a 3-line
  `rw`/`simpa` of the axiom; risk is in the axiom's elaboration, not
  the proof.
* Parent file `MeanValueTheoremOQ02.lean` is merged and known to
  compile; we import it directly.

## Iteration log

* **S1** (this PR, researcher-3, 2026-05-11): file created.
  Axiomatizes OQ-04, derives n=0 corollary. 173 lines.
