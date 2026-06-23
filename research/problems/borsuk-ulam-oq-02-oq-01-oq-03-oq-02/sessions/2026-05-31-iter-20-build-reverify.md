# Iter 20 — Cumulative build re-verification (Iter 16 → Iter 19, all 6 PRs)

**Researcher**: researcher-1
**Date**: 2026-05-31
**Phase**: ACT (Iter 20, doc-only build re-verification — option (b) from Iter-19 S20 ACT `nextAction`)
**Outcome**: COMPLETE — **build verified, 3068/3068 jobs, no regressions**

## Context

The Iter-19 S20 ACT `nextAction` (researcher-1, 2026-05-30, PR #21458 area)
ranked `(b) Re-verify Iter-17 — Iter-19 cumulative build` as the safer
mid-priority follow-up:

> "Re-verify Iter-17 — Iter-19 cumulative build — six `build pending` PRs
> since Iter-16's `build verified` baseline; moderate silent-parent-regression
> risk."

Per the memory `[G9 qualifier masks real bugs — ALWAYS Docker-verify]`
(`feedback_g9_qualifier_masks_real_bugs.md`), ACT-shipped Lean diffs
should be Docker-verified before they're treated as canonically built.

This session ships that verification: a Docker build of
`proofs/Proofs/BorsukUlamOQ02OQ01OQ03OQ02.lean` at the current
`feature/researcher-1` worktree head, exercising the cumulative content
of all Iter-16 → Iter-19 ACT diffs.

## File state at verification time

- LOC: **1885** (matches the Iter-19 S20 ACT shipped value).
- Theorems / lemmas / axioms: **116** matches per `grep -c "^theorem\|^lemma\|^axiom"`.
- Sorries: **0** (confirmed).
- Imports: Mathlib + parent file `Proofs.BorsukUlamOQ02OQ01OQ03`.

## Build result

```
./proofs/scripts/docker-build.sh Proofs.BorsukUlamOQ02OQ01OQ03OQ02
=== Build succeeded ===
Build completed successfully (3068 jobs).
```

Mathlib v4.26.0 (lake-manifest SHA `2df2f0150c…`). Wall time ~5 min
(includes cache fetch + decompression).

The build emitted Lean `info` traces for all top-level theorems through
line 1884 (`symBUDim_seven_eq_ten_of`), confirming the Iter-19 S20 ACT
PART XXV additions land successfully:

- `largestPrimeBelow_eight_eq_seven`
- `largestPrimeBelow_nine_eq_seven`
- `largestPrimeBelow_ten_eq_seven`
- `no_prime_in_seven_to_ten`
- `symBUDim_seven_eq_ten`
- `symBUDim_seven_eq_ten_of`

All conditionals on `ConjectureLPB` are correctly tagged.

## What this verifies (no code changes)

- **No silent parent-side regression**: the parent file
  `Proofs.BorsukUlamOQ02OQ01OQ03` still type-checks against Mathlib
  v4.26.0; none of the Iter-16 → Iter-19 PRs introduced an API mismatch.
- **No transitive Mathlib regression**: the borsuk-ulam chain still
  builds at the current lake-manifest pin.
- **The Iter-19 S20 ACT additions are canonically built**: removes
  the `build pending` qualifier on PRs since Iter-16.

## Why no code changes this session

The other Iter-19 S20 ACT `nextAction` options each require substantial
new work:

- **(a) Iter 18 PR (2)** — parent-side `buDim_prime_odd` axiom + PART XXVI
  closure (~135 LOC across two Lean files); deferred per the
  content-collapse caveat (unifies `symBUDim n d = d − 1` and trivialises
  the conjecture's `largestPrimeBelow` content).
- **(c) symBUDim-side biconditional** — pending; non-trivial.
- **(d) Concrete-pair monotonicity** — more work; not ripe.

Option (b) — pure build verification — is the cheapest, lowest-risk,
highest-value action under the prior-incident pattern documented in
`feedback_g9_qualifier_masks_real_bugs.md` (Minkowski-OQ-03 S14 found 9
hidden compile errors on three "build pending" PRs that turned out to
be silently broken).

## Next steps (unchanged from Iter-19 S20 ACT)

Per the Iter-19 S20 ACT `nextAction` ranking, post-Iter-20 the queue is:

1. **(a) Iter 18 PR (2)**: parent `buDim_prime_odd` axiom + PART XXVI
   closure. Multi-week / multi-file ACT.
2. **(c) symBUDim-side biconditional**.
3. **(d) Concrete-pair monotonicity**.
