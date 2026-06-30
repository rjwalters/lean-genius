# Research State: arithmetic-series-oq-02-oq-04-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-13
**Iteration**: 2

## Current Focus
Statement fixed and a complete proof path identified (see knowledge.md). The draft
Lean proof has already been written to `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ01.lean`
(PR #23066). It remains build-unverified pending the 2026-06-13 Docker/Aristotle outage.

## Active Approach
Reduce `multichoose n k * k!` to the parent identity `choose_descFactorial` at
`m = n+k-1`, then reindex the descending-factorial product via `Finset.prod_range_reflect`
to obtain `∏ i ∈ range k, (n+i)`. Draft proof written in knowledge.md and committed to
the Lean file as `multichoose_factorial` (plus `_one/_two/_three` specializations and
`native_decide` sanity checks). 0 sorries.

## Attempt Count
- Total attempts: 1 (survey/draft, unbuilt)
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- **Verification infra down (2026-06-13):** Docker daemon down; Aristotle backend returns
  404. The committed draft proof cannot be compiled, so the file is intentionally NOT yet
  registered in `proofs/Proofs.lean` (so it cannot break the build). This is an
  external/transient blocker, not a mathematical one.

## Next Action
When Docker is back: build the existing draft with
`./proofs/scripts/docker-build.sh Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ01`,
reconcile any Mathlib lemma-name drift, register it in `proofs/Proofs.lean`, then add the
gallery `meta.json` entry and advance to COMPLETED.
