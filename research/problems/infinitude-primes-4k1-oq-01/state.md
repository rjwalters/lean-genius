# Research State: infinitude-primes-4k1-oq-01

## Current State
**Phase**: ACT (S2 SCAFFOLD — `proofs/Proofs/InfinitudePrimes4k1OQ01.lean` SHIPPED build-verified; 0 axioms, 0 sorries)
**Path**: full
**Since**: 2026-05-30 (S1 OBSERVE; problem created 2026-04-12T14:53:27-07:00, 48d idle prior to S1)
**Last Updated**: 2026-06-01 (S2 SCAFFOLD ACT — Fermat two-squares biconditional shipped; 3062/3062 build jobs verified; iteration 1→2, researcher-1)
**Iteration**: 2 (S2 ACT)

## Current Focus

S2 SCAFFOLD ACT (2026-06-01, researcher-1, this iter): Shipped `proofs/Proofs/InfinitudePrimes4k1OQ01.lean` (74 LOC, 0 axioms, 0 sorries) implementing the S1 paste-ready blueprint verbatim with two ≤2-LOC `omega`-hypothesis-enrichment refinements. Build-verified 3062/3062 jobs in Docker at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (9.1s compile time for the new file via Mathlib cache hit). Aggregator `proofs/Proofs.lean` updated with one new `import Proofs.InfinitudePrimes4k1OQ01` line alphabetically slotted between the existing `Proofs.InfinitudePrimes4k1` and `Proofs.InfinitudePrimes4k1OQ03` entries.

**Slug now substantively complete at the Lean-file level**. Two declarations:
- `InfinitudePrimes4k1OQ01.sq_mod_four` (lemma): `n^2 % 4 ∈ {0, 1}` via `interval_cases (n % 4)` + `omega`.
- `InfinitudePrimes4k1OQ01.fermat_two_squares` (theorem): `p odd prime → (p % 4 = 1 ↔ ∃ a b, p = a^2 + b^2)`. Forward direction wraps Mathlib's `Nat.Prime.sq_add_sq` (pinned bearer F1 at `Mathlib/NumberTheory/SumTwoSquares.lean:35`). Backward direction is a mod-4 case analysis using `sq_mod_four` + `Nat.pow_mod` + parity.

**Two minor blueprint refinements at paste time** (each ≤2 LOC):
1. `sq_mod_four` needed an explicit `have h_pow : n^2 % 4 = (n % 4)^2 % 4 := by rw [Nat.pow_mod]` before `interval_cases` for `omega` to close.
2. `fermat_two_squares` backward direction needed `have hamod : a % 2 < 2` + `hbmod` in scope for the final `omega`.

These are exactly the `omega`-hypothesis-enrichment refinements the S1 §5 risk register anticipated; no mathematical drift.

## Active Approach

**Approach 1 (Direct Mathlib wrapper)** — per S1 PR #21168 §4. **SHIPPED**. Implementation verbatim from S1 blueprint with two ≤2-LOC paste-time refinements.

## Attempt Count

- Total attempts: 1 (S2 SCAFFOLD ACT — successful first attempt)
- Current approach attempts: 1
- Approaches tried: 1 (Approach 1 succeeded; no other approaches attempted)

## Blockers

None. Slug is substantively complete at the Lean-file level.

## Next Action

**Gallery entry creation** (enricher task, NOT researcher): create `src/data/proofs/infinitude-primes-4k1-oq-01/` with `meta.json`, `annotations.source.json`, `index.ts`. This is the enricher's lane per CLAUDE.md role split.

**Slug decommission readiness**: once gallery entry is created (post-merge), the slug can move from `in-progress` to `completed` via `claim-problem.sh update <slug> completed`. Until then, status stays `in-progress`.

If a researcher claims this slug for an S3 iteration before the enricher acts, a sensible doc-only sweep is a STATE-SYNC confirming no drift between research artifacts. No further ACT iteration is warranted.

## Session Log

| Iter | PR | Type | Author | Title summary |
|------|------|------|--------|---------------|
| S1 | #21168 (MERGED) | OBSERVE | researcher-1 | Mathlib `SumTwoSquares.lean` API pin-survey at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; 6 bearers pin-verified (F1 `Nat.Prime.sq_add_sq` + 5 supporting); paste-ready S2 SCAFFOLD Lean (~50 LOC, 0 sorries) (doc-only) |
| S2 | this PR | ACT | researcher-1 | SCAFFOLD shipped: `proofs/Proofs/InfinitudePrimes4k1OQ01.lean` 74 LOC, 0 axioms, 0 sorries; `Proofs.lean` aggregator updated. Build-verified 3062/3062 jobs in Docker at lake-pinned SHA `2df2f0150c…` (9.1s compile via cache hit). Two ≤2-LOC `omega`-hypothesis-enrichment refinements at paste time. |
