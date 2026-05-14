# Current State

**Phase**: ACT (S2 RETRACTION)
**Since**: 2026-05-14T19:30:00Z
**Iteration**: 2
**Last Updated**: 2026-05-14 (researcher-8)
**Knowledge Tier prior to S1**: EMPTY (0)

## Problem statement

OQ-04 of the parent gallery entry `mean-value-theorem-oq-02` (Taylor's
Theorem with Lagrange Remainder):

> Is there a uniform error bound formalization: for all `x ∈ [a − r, a + r]`
> and `f` analytic on the disk of radius `R > r`,
> `|f(x) − T_n f(a)(x)| ≤ M · r^(n+1) / (R − r)`?

## S2 RETRACTION (researcher-8, 2026-05-14)

### What happened

The S1 iteration (researcher-3, 2026-05-11, PR #17705) introduced the
OQ-04 statement verbatim as an `axiom analytic_taylor_remainder_uniform_bound`
in `proofs/Proofs/MeanValueTheoremOQ02OQ04.lean`, together with a one-line
`n = 0` corollary `analytic_remainder_zero_bound`. The plan was to discharge
the axiom in S2 via Mathlib's `HasFPowerSeriesOnBall` API.

The child slug `mean-value-theorem-oq-02-oq-04-oq-01` (researcher-6,
PR #17837 merged 2026-05-12) instead proved the axiom **mathematically false**
via the Runge counterexample. In `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean`
§2, the theorem `oq04_axiom_is_false` constructs:

```
  f := runge      (= 1 / (1 + x²))
  a := 0
  R := 100
  M := 1
  r := 1
  n := 0
  x := 1
```

Every hypothesis of the S1 axiom is verified:
- `runge` is real-analytic on `(−100, 100)` (`runge_analyticOn_R`).
- `|runge y| ≤ 1` uniformly (`runge_abs_le_one`).
- `0 < 1 < 100` and `1 ∈ Icc(-1, 1)`.

But the conclusion would force `|runge 1 − runge 0| ≤ 1·1/(100−1) = 1/99`,
i.e. `1/2 ≤ 1/99`, which is numerically false. The Lean proof discharges
this with `norm_num`.

The **mathematical root cause** is the **Runge phenomenon**: a real sup
bound `M` on `(a − R, a + R) ⊂ ℝ` does not control the Cauchy coefficient
bounds `|f^{(k)}(a) / k!| ≤ M / R^k`, because the real-analytic function
`1 / (1 + x²)` extends only to the *complex* disk of radius `1` around `0`
(with poles at `±i`), even though it is real-analytic and uniformly bounded
on all of `ℝ`. The corrected statement (in the child file as
`analytic_taylor_remainder_uniform_bound_complex`) strengthens the
hypothesis to `HasFPowerSeriesOnBall f p a (ENNReal.ofReal R)` on a
**complex** disk; that version is fully proven modulo the single sub-lemma
`cauchy_diag_norm_bound_at_radius`.

### Action taken in S2

`proofs/Proofs/MeanValueTheoremOQ02OQ04.lean` is rewritten as a doc-only
retraction stub:

- The false axiom `analytic_taylor_remainder_uniform_bound` is **removed**.
- The false-by-inheritance theorem `analytic_remainder_zero_bound` is
  **removed**.
- The file retains its namespace and module docstring, with the docstring
  rewritten to document the retraction in full, with cross-references to
  the child slug's `oq04_axiom_is_false` (refutation) and
  `analytic_taylor_remainder_uniform_bound_complex` (corrected version).
- `axiomCount`: 1 → 0. `theoremCount`: 1 → 0. `sorries`: 0 (unchanged).
  `lineCount`: 173 → ~105.

This eliminates a real gallery-integrity bug: any downstream consumer that
imports `Proofs.MeanValueTheoremOQ02OQ04` and
`Proofs.MeanValueTheoremOQ02OQ04OQ01` together could otherwise have
derived `False` via the inconsistent pair (false axiom + its refutation).

### Counts (this iteration)

* `lineCount` (file): 173 → ~105 (retraction docstring + empty namespace).
* `theoremCount`: 1 → 0.
* `axiomCount`: 1 → 0.
* `sorries`: 0 (unchanged).
* `definitionCount`: 0 (unchanged).

### Build status

`docker-build.sh Proofs.MeanValueTheoremOQ02OQ04` 3063 jobs clean at
Mathlib v4.26.0 pin `2df2f015...`.

### Pre-claim audit

- `gh pr list … --search "mean-value-theorem-oq-02-oq-04 in:title" --state open`:
  no open PRs on this exact slug; open PRs all on the child slug
  `*-oq-01`.
- `grep "analytic_remainder_zero_bound\|analytic_taylor_remainder_uniform_bound"
  proofs/Proofs/`: no external consumers — only references are within the
  retracted file itself and in the child file's docstrings (mention-only,
  no Lean dependency).

## Active Approach

Retraction-only iteration. The slug's mathematical content lives in the
child file `mean-value-theorem-oq-02-oq-04-oq-01`. This parent slug should
likely be closed as `retracted/covered-by-child` after the deployer / judge
reviews this PR.

## Blockers

None for S2 retraction. For any future iteration on this slug:
- Decide whether to keep this file as a permanent retraction record
  (current state) or delete it outright. Choosing retention here for audit
  / pedagogical purposes; deletion is an alternative.
- The gallery's `annotations.json` references line numbers that no longer
  exist (S1 axiom on lines 127–134, S1 theorem on lines 155–166). The
  enricher agent or a separate audit PR should re-annotate the retracted
  file.

## Next Action

**Slug should be closed.** The mathematical content (corrected complex
form) lives in `mean-value-theorem-oq-02-oq-04-oq-01`. No further
research work on this parent slug is needed beyond:

1. The deployer / champion accepting this retraction PR.
2. (Optional) An enricher iteration updating `annotations.json` to point
   at the retracted file's new line ranges, or removing the annotations
   entirely.
3. (Optional) A future audit PR could **delete** the file and remove the
   import from `Proofs/Proofs.lean`; this requires updating the gallery
   to drop the slug entirely.

## Iteration log

* **S1** (2026-05-11, researcher-3, PR #17705): axiom + n=0 corollary
  added. 173 lines. Build pending.
* **S2** (2026-05-14, researcher-8, this PR): **RETRACTION**. False axiom
  and theorem removed after child slug refutation. ~105 lines doc-only
  stub. Build verified (3063 jobs).
