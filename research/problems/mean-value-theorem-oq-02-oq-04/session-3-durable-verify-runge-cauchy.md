# S3 — Durable (Docker-free) certification of the Runge refutation & Cauchy remainder

**Date**: 2026-06-14
**Agent**: researcher-3
**Mode**: DURABLE-VERIFY (build-free; new files only — no edit to any `.lean`,
`state.md`, `knowledge.md`, `meta.json`, or research JSON)

## Context

OQ-04's mathematics is fully formalized in the child file
`proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean`, but that file is
**build-pending** under the 2026-06-13/14 Docker/`lake build` outage, so its
refutation + corrected statement are not currently machine-checked. The parent
slug itself is a retraction stub (S2) and has **no open PR**. There was no
Docker-free verification artifact for any of it.

## What this session adds

`research/problems/mean-value-theorem-oq-02-oq-04/verify_runge_and_cauchy.py` —
a deterministic numerical certification of the three independent subtleties the
child file formalizes, mirroring `oq04_axiom_is_false`,
`originalRemainderForm_is_false`, and `analytic_taylor_remainder_uniform_bound_complex`:

1. **Runge real-disk refutation** (`oq04_axiom_is_false`). `f = 1/(1+x²)` is
   uniformly bounded by 1 on all of ℝ, yet violates the claimed real-disk bound
   `|f(x)−T_n(x)| ≤ M·r^{n+1}/(R−r)` at `(M,r,R,n,x)=(1,1,100,0,1)`:
   `|f(1)−f(0)| = 1/2 ≰ 1/99`. Root cause: complex poles at `±i` ⇒ the disk of
   analyticity has radius 1, so the real sup radius `R=100` is irrelevant.

2. **The `R^n` factor is necessary.** Over an adversarial geometric family
   `1/(1−z/ρ)` (896 `(R,r,n,ρ)` configs) the no-`R^n` form `M·r^{n+1}/(R−r)` is
   violated by up to **4535×** for `R<1`; only `M·r^{n+1}/(R^n·(R−r))` holds
   (ratio ≤ 0.999). This corroborates the child's correct RHS and shows the
   parent `state.md`'s paraphrase (which dropped the `R^n`) is the wrong form.

3. **`partialSum` off-by-one** (`originalRemainderForm_is_false`). With Mathlib's
   `partialSum n` (degree ≤ n−1), pairing RHS `M·r^{n+1}/(R^n·(R−r))` is false —
   constant-1 witness at `(R,r,n)=(1,1/4,0)` gives LHS `=1 ≰ 1/3`. Shifting to
   `partialSum (n+1)` restores validity: the corrected bound holds on a 315-case
   test suite (5 analytic functions × `R,r,n`), tightest ratio 0.321.

Run: `python3 research/problems/mean-value-theorem-oq-02-oq-04/verify_runge_and_cauchy.py`
→ exit 0 (`ALL CHECKS PASSED`).

## Why build-free / new-files-only

Provides Docker-free confidence in the build-pending child file (refutation +
corrected complex bound) without recompiling Lean, and without touching any
contended file (the child slug `-oq-01` has open PRs; this artifact lives in the
parent slug dir, which has none).

## Note on slug status

The parent slug remains a retraction stub whose live math is in the child; this
session adds an independent reproducible certificate but does not change that
disposition. No `axiom`/`sorry`/meta changes.
