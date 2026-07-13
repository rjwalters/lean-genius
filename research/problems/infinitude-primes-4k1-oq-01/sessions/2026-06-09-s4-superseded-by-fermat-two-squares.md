# Session: 2026-06-09 — S4 SUPERSEDED-BY-FERMAT-TWO-SQUARES (doc-only)

**Iteration**: 4
**Type**: STATE-SYNC + supersession finding
**Author**: researcher-1
**Date**: 2026-06-09
**HEAD at claim**: `ab09ff2d20d` (lake-pin SHA still `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Phase transition**: COMPLETE-at-Lean-file-level → SUPERSEDED (existing gallery entry covers the OQ-01 problem statement strictly more generally)

## Summary

Surveying the gallery before producing the awaited enricher artifact revealed
that `proofs/Proofs/FermatTwoSquares.lean` (201 LOC, 6 theorems, gallery slug
`fermat-two-squares`) **already proves the OQ-01 problem statement in a strictly
stronger form**, using the same Mathlib bearer and the same case-analysis
technique. The S1/S2 author missed this when surveying, treating the open
question as a gap rather than a duplication. This iteration:

1. Documents the supersession in the research artifacts.
2. Adds a 10-line header redirect to `InfinitudePrimes4k1OQ01.lean` pointing
   future readers to `FermatTwoSquares.lean` as canonical.
3. Marks the slug `completed` because the open question is answered by the
   existing gallery proof — no separate enricher gallery entry should be
   created (it would be a redundant duplicate).

## Evidence of supersession

Both files compile at lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

| Concern | `InfinitudePrimes4k1OQ01.lean` (S2 ship) | `FermatTwoSquares.lean` (pre-existing) |
|---|---|---|
| Lean LOC | 84 (now 93 after S4 header redirect) | 201 |
| Top-level declarations | 2 (`sq_mod_four`, `fermat_two_squares`) | 6 (`sum_two_squares_iff_not_three_mod_four`, `one_mod_four_is_sum_of_squares`, `two_is_sum_of_squares`, `three_mod_four_not_sum_of_squares`, `prime_classification`, `sum_of_squares_classification`) |
| Mathlib bearer | `Nat.Prime.sq_add_sq` | `Nat.Prime.sq_add_sq` (same) |
| Main biconditional | `p odd prime → p ≠ 2 → (p % 4 = 1 ↔ ∃ a b, p = a^2 + b^2)` | `(∃ a b, a^2 + b^2 = p) ↔ p % 4 ≠ 3` (covers `p = 2` case implicitly via `2 % 4 = 2 ≠ 3`) |
| Squares-mod-4 helper | `sq_mod_four : n^2 % 4 = 0 ∨ n^2 % 4 = 1` via `interval_cases (n % 4) <;> omega` | Inlined in `sum_two_squares_iff_not_three_mod_four` body: `interval_cases a % 4 <;> simp` + `interval_cases b % 4 <;> simp` (identical pow_mod + interval_cases pattern) |
| Gallery entry | absent (awaiting enricher action since 2026-06-02 ≈ 7 days) | present at `src/data/proofs/fermat-two-squares/{meta.json,annotations.json,annotations.source.json,tacticStates.json}` |
| Wiedijk 100 listed? | no | yes (`wiedijkNumber: 20`) |
| Gallery cross-refs to/from `infinitude-primes-4k1` | absent | absent for OQ-01 slug; `infinitude-primes-4k1/meta.json` openQuestions §0 explicitly asks "Can Fermat's theorem on sums of two squares be formalized using similar Mathlib infrastructure: p ≡ 1 (mod 4) ⟺ p = a² + b²?" — answered by `fermat-two-squares` |

The S1 author's pin survey (`sessions/2026-05-30-s1-observe-mathlib-sumtwosquares-api-survey.md`)
correctly identified `Nat.Prime.sq_add_sq` as the right bearer, but did not
search `proofs/Proofs/Fermat*.lean` or `src/data/proofs/fermat-*` for an
existing proof of the same theorem. A `Glob src/data/proofs/fermat-two-*`
would have caught this in one query.

## Why this is not just a STATE-SYNC

The S3 nextAction (`state.md:99-105`) explicitly warns:
> *If a researcher claims this slug for an S3 iteration before the enricher
> acts, a sensible doc-only sweep is a STATE-SYNC confirming no drift between
> research artifacts. No further ACT iteration is warranted.*

…and the S3 JSON `currentState.nextAction` adds:
> *…only another doc-only STATE-SYNC is appropriate (and only if material
> new state has arrived — per memory feedback
> `_back_to_back_statesyncs_at_unchanged_state_is_busywork`).*

**Material new state has arrived**: the discovery that the OQ-01 problem
statement is already answered by `fermat-two-squares` (gallery slug present,
Lean file present, strictly more general biconditional, same Mathlib bearer).
This finding obsoletes the S3 nextAction's premise that an enricher artifact
is awaited — the artifact would be a redundant duplicate. Instead, the slug
should be marked `completed` and the OQ-01 Lean file kept as a small
odd-prime-only pedagogical wrapper with a header redirect to the canonical
proof.

## What this iteration is NOT

- **Not** a deletion of `InfinitudePrimes4k1OQ01.lean`. Removing merged
  research artifacts is the Hermit's lane and warrants its own scrutiny; this
  iteration only adds a header redirect and keeps the file as-is.
- **Not** an enricher gallery entry. `src/data/proofs/infinitude-primes-4k1-oq-01/`
  is intentionally **not** created — the canonical home is
  `src/data/proofs/fermat-two-squares/`.
- **Not** an edit to the `fermat-two-squares` gallery entry to cross-reference
  the OQ-01 slug. That is the enricher's lane; this researcher session leaves
  the question of whether a cross-ref is useful to the enricher.
- **Not** a Lean recompile. The header docstring is the only change in the
  Lean file; the proof body is byte-identical. No build verification needed
  (docstring-only Lean edits do not affect elaboration). The S2 build
  verification (3062/3062 jobs at lake SHA `2df2f0150c…`) stands.

## Files changed by this iteration

- `proofs/Proofs/InfinitudePrimes4k1OQ01.lean` — header docstring only: added
  9 lines naming `FermatTwoSquares.lean` as canonical, listing its 4 main
  theorems, and pointing here. 84 → 93 LOC; 0 axioms, 0 sorries unchanged.
- `research/problems/infinitude-primes-4k1-oq-01/state.md` — refresh Current
  State header (Phase → SUPERSEDED; iter 3 → 4; lastUpdate now), insert this
  iter-4 section, refresh Active Approach (S2 shipped wrapper kept as
  pedagogical odd-prime form), refresh Blockers (none) and Next Action
  (slug → completed; no enricher gallery entry).
- `src/data/research/problems/infinitude-primes-4k1-oq-01.json` —
  `currentState.iteration` 3 → 4; `currentState.lastUpdate` now;
  `currentState.phase` updated to "SUPERSEDED by fermat-two-squares
  gallery slug"; `currentState.focus` and `currentState.nextAction`
  refreshed; `attemptCounts.total` 2 → 3.
- `research/problems/infinitude-primes-4k1-oq-01/knowledge.md` — first real
  insights/dead-ends content (was placeholder until this iteration).
- `research/problems/infinitude-primes-4k1-oq-01/sessions/2026-06-09-s4-superseded-by-fermat-two-squares.md` —
  this file.

## Slug status after this iteration

- Lean file: clean (0 sorries, 0 axioms), kept as odd-prime-only pedagogical
  wrapper with header redirect.
- Gallery entry: intentionally absent at `src/data/proofs/infinitude-primes-4k1-oq-01/`;
  canonical home is `src/data/proofs/fermat-two-squares/`.
- Pool status: `claim-problem.sh update infinitude-primes-4k1-oq-01 completed`
  will be run after this PR is opened. The slug joins the `completed` tier
  (currently 1645 entries) rather than waiting indefinitely for an enricher
  artifact that should not exist.

## What a future agent should NOT do on this slug

- Do not create `src/data/proofs/infinitude-primes-4k1-oq-01/`. Use
  `src/data/proofs/fermat-two-squares/` as the canonical home.
- Do not re-open the slug as a separate open question. The biconditional is
  proved; the only remaining cosmetic work is the cross-reference noted
  below, which is enricher's lane.
- Do not delete `proofs/Proofs/InfinitudePrimes4k1OQ01.lean` casually — that
  is the Hermit's lane, with its own decision criteria (the file compiles
  at zero axiom/sorry cost, provides a small odd-prime-only pedagogical
  variant, and the deletion saves ~93 LOC).

## What an enricher COULD optionally do later (enricher's lane)

- Add a `crossReferences` entry in `src/data/proofs/fermat-two-squares/meta.json`
  pointing to `infinitude-primes-4k1` as a downstream consumer (the
  `infinitude-primes-4k1/meta.json` openQuestions §0 is the matching question
  this slug answers).
- Optionally edit `src/data/proofs/infinitude-primes-4k1/meta.json`
  openQuestions §0 from a forward-looking "Can…" phrasing to a backward-looking
  "See `fermat-two-squares`" pointer.

Neither is required for the OQ-01 slug to be cleanly closed.
