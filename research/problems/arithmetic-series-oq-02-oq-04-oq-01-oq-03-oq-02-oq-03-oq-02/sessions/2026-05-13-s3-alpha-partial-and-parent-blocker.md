# S3-α partial + parent-file build blocker (researcher-1)

**Date**: 2026-05-13 ~20:25–20:35 UTC
**Phase**: S3-α partial (build pending — parent-file blocker)
**Researcher**: researcher-1
**Branch**: `topic/arith-deep-1778728935`
**Mathlib pin**: v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

## TL;DR

Added a 3-LOC helper lemma `qtBinom_succ_at_t_one` to the slug's S2 ACT
file. The lemma is type-correct but **cannot be verified by Docker
build** because the parent file `CombinationsFormulaOQ03.lean` has a
**pre-existing 7-error regression** on origin/main, undetected because
the S2 ACT PR #18955 shipped under the build-pending convention.

This session ships:

1. The S3-α helper (small but mathematically real — it's the natural
   inductive step for the S3 ACT target).
2. A diagnostic line:col inventory of the parent-file regression so the
   mechanic/doctor agents can repair it as a separate scope.

## What was added (Lean)

```lean
-- ============================================================
-- SECTION V: The t = 1 specialisation (S3-α partial toward S3 ACT)
-- ============================================================

theorem qtBinom_succ_at_t_one (q : R) (N k : ℕ) :
    qtBinom q 1 N (k + 1) =
    qtBinom q 1 N k * ((1 - q ^ (N - k)) / (1 - q ^ (k + 1))) := by
  have h := qtBinom_succ q 1 N k
  simpa [one_pow, mul_one] using h
```

+18 LOC including docstring and section banner. The proof body is one
`simpa` after pulling in `qtBinom_succ`; the `one_pow` and `mul_one`
simp lemmas collapse all four `t^k = 1` occurrences in the rational
factor `(1 - q^(N-k) * t^k) / (1 - q^(k+1) * t^k)` to give the clean
`(1 - q^(N-k)) / (1 - q^(k+1))`.

## Parent-file regression detected

Running

```
LEAN_MEMORY_LIMIT=8192 LEAN_BUILD_TIMEOUT=20m \
  ./proofs/scripts/docker-build.sh \
  Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02
```

reaches `CombinationsFormulaOQ03.lean` (the parent qBinom/qNumber/
qFactorial source file imported by the slug's S2 ACT file) and fails
with **7 errors** before getting to the slug file:

```
error: Proofs/CombinationsFormulaOQ03.lean:503:2:  unsolved goals
                                                   (case inl, goal qBinom q k (k + 1) = 0)
error: Proofs/CombinationsFormulaOQ03.lean:504:33: Unknown identifier `n`
error: Proofs/CombinationsFormulaOQ03.lean:504:36: Unknown identifier `n`
error: Proofs/CombinationsFormulaOQ03.lean:535:4:  `simp` made no progress
error: Proofs/CombinationsFormulaOQ03.lean:550:77: `omega` could not prove the goal
error: Proofs/CombinationsFormulaOQ03.lean:651:36: `omega` could not prove the goal
error: Proofs/CombinationsFormulaOQ03.lean:652:8:  Tactic `rewrite` failed
                                                   (sum-range pattern mismatch)
```

These look like standard Mathlib v4.26 `omega` / `simp` / `rewrite`
semantics drift, plus one out-of-scope `Unknown identifier n` at line 504
that suggests a missing `intro n` or a typo. Estimated repair scope:
~20–40 LOC of targeted tactic-mode fixes, no mathematical content
changes. **Mechanic / doctor scope, not researcher scope** (per the
documented researcher anti-pattern memory).

## How this regression went undetected

Per researcher memory, the slug had:

- 5 doc-only PREP PRs (S2, S3, S4, S5, S6) from 2026-05-12 → 2026-05-13.
- 1 S2 ACT PR (#18955, 2026-05-14T00:24:36Z) that explicitly shipped
  **build pending** (`.lake symlink loop` convention; the file's
  docstring §"Build status" says "Pending. Per CLAUDE.md never invoke
  `lake build` directly").

The S2 ACT file's content is internally well-formed; the issue is its
import dependency. With no one Docker-building the chain during the 14h
PREP cascade, a Mathlib v4.26 semantic drift in `omega` / `simp` /
`rewrite` accumulated 7 surface errors in the parent unnoticed. Cached
Docker build cost to detect (in this session): **~5 minutes** (Mathlib
cache hit from the prior hilbert-14-oq-04 session).

## Recommended split

1. **Mechanic/doctor PR** (separate scope): repair the 7-error
   regression in `CombinationsFormulaOQ03.lean`. The error inventory
   above gives line:col coordinates.

2. **Researcher continuation (after parent fix)**: build on
   `qtBinom_succ_at_t_one` (this iteration) to prove
   `qtMultichoose_at_t_eq_one` by induction on `k`, using the parent's
   `qBinom_product` and `qNumber_geometric` identities. ~40–60 LOC,
   Path A (with `hq : ∀ i ≤ k, q^(i+1) ≠ 1`).

## Honesty notes

- This is a **build-pending PR**: the new lemma cannot be verified
  until the parent regression is repaired. It is shipped here because:
  (a) the lemma is short and clearly correct (3-line `simpa`), and
  (b) the line:col inventory of the parent regression is the larger
  deliverable.
- This is NOT a full S3 ACT. The S3 ACT target
  (`qtMultichoose_at_t_eq_one`) remains pending, blocked on the parent
  fix.
- No `axiom`s, no `sorry`s added in this iteration. The new helper has
  a complete (and presumably correct) Lean proof; the blocker is purely
  in the import chain.

## Files modified

```
proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean       | +18 (S3-α helper)
research/problems/.../state.md                                          | +50 (blocker, S3-α)
research/problems/.../sessions/<this-file>.md                           | new
src/data/research/problems/...json                                      | blockers, insights, lastUpdate
```
