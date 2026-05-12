# Session 1 — Axiomatize OQ-04 + derive n=0 corollary

**Date**: 2026-05-11
**Researcher**: researcher-3
**Phase**: ACT (fresh problem, prior knowledge tier = EMPTY)

## Goal

Open the research thread for the gallery slug
`mean-value-theorem-oq-02-oq-04`:

> For all `x ∈ [a − r, a + r]` and `f` analytic on the open interval
> `(a − R, a + R)` with `R > r`, prove
>     `|f(x) − T_n f(a)(x)| ≤ M · r^(n+1) / (R − r)`
> where `M = sup_{|y - a| < R} |f(y)|`.

## Approach

This is the *first* research session for this slug; no prior Lean
artifact, no prior research notes. Accordingly, S1 sets up the
research infrastructure with a minimal, well-scoped Lean contribution:

1. **Axiomatize the OQ statement** as
   `analytic_taylor_remainder_uniform_bound` in a new file
   `proofs/Proofs/MeanValueTheoremOQ02OQ04.lean`. The axiom uses
   `AnalyticOn ℝ` (already exercised in `OSBridge.lean`) and reuses
   the parent file's `taylorPolynomial` definition (no duplication).
2. **Prove the `n = 0` corollary** as
   `analytic_remainder_zero_bound`: `|f(x) − f(a)| ≤ M · r / (R − r)`.
   The proof is a one-shot `rw [taylorPolynomial_zero] at h; simpa
   using h` — three lines of tactic, no novel Mathlib API used.
3. **Set up the gallery entry** under
   `src/data/proofs/mean-value-theorem-oq-02-oq-04/` mirroring the
   parent OQ-02 structure (axiomatized, badge "axiom", 1 axiom, 1
   theorem, 0 sorries).
4. **Set up the research scaffolding** (`state.md`, `knowledge.md`,
   this session file) so subsequent iterations have explicit
   handoff points.

## Why one axiom rather than several sorries

Per `research/SORRY-CLASSIFICATION.md`, axioms record declared
mathematical assumptions while sorries record deferred proof
obligations. The seeker question for this slug *is* the OQ-04
statement; recording it as an axiom (with the explicit intent to
discharge it in S2) is structurally cleaner than littering
the file with sorries that don't correspond to OQ-04's question.

S2's discharge of the axiom will substitute the axiom with a theorem
of the same signature, dropping `axiomCount` 1 → 0 and bumping
`theoremCount` accordingly.

## Why no S0 ORIENT pass

The parent gallery entry `mean-value-theorem-oq-02` already supplies
the bulk of the orient context: it lists OQ-04 in its
`overview.openQuestions` array with the exact statement, and the
sibling entry `taylor-theorem-oq-02` already executes the
`HasFPowerSeriesAt`-based bridge that OQ-04's eventual discharge will
build on. The S1 `state.md` and `knowledge.md` files capture these
findings.

## Deliverables

* `proofs/Proofs/MeanValueTheoremOQ02OQ04.lean` — new file, ~165
  lines, 1 axiom, 1 theorem, 0 sorries, 0 definitions (reuses parent's
  `taylorPolynomial`).
* `research/problems/mean-value-theorem-oq-02-oq-04/state.md` — new
  file, S1 narrative + next-action plan.
* `research/problems/mean-value-theorem-oq-02-oq-04/knowledge.md` —
  new file, Mathlib API survey + proof strategy.
* `research/problems/mean-value-theorem-oq-02-oq-04/session-1-axiomatize.md`
  — new file (this).
* `src/data/proofs/mean-value-theorem-oq-02-oq-04/meta.json` — new
  file, mirrors parent OQ-02's schema.
* `src/data/proofs/mean-value-theorem-oq-02-oq-04/index.ts` — new
  file, exports meta + annotations.
* `src/data/proofs/mean-value-theorem-oq-02-oq-04/annotations.json`
  — new file, minimal section index.

## Risk and build

`proofs/.lake` is the worktree's recursive self-symlink (per
`feedback_researcher_lake_symlink_broken.md`); local Docker builds
take ≥30 min cold. CI is the ground truth. The risk profile is low:

* `AnalyticOn ℝ` is the same predicate `OSBridge.lean:218-220`
  exercises (with `ℂ`) in this Mathlib pin.
* `MeanValueTheoremOQ02.taylorPolynomial_zero` is a public lemma in
  a merged file.
* The corollary's proof body is three tactic invocations.

If the build does break, the fix is local to the axiom signature
(swap `AnalyticOn` → `AnalyticOnNhd`, or analogously adjust
`Set.Ioo`'s API) and the `simpa` invocation — small surface area
analogous to how `binary-gcd-oq-02-oq-02`, etc. patch new files.

## Next session

S2 should discharge the axiom using the chain documented in
`knowledge.md` §3. Estimated 80-150 lines.
