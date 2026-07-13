# Current State

**Phase**: COMPLETED
**Since**: 2026-04-27T15:55:37Z (terminal phase; iteration bumps for STATE-SYNC catch-up cycles)
**Iteration**: 4

## Current Focus

Slug is at terminal phase. The Lean file `proofs/Proofs/Erdos1141Problem.lean` (210 LOC, 35 theorems, 1 axiom, 3 defs, 0 sorries) was last edited at merge `11d5cd15fd1` (PR #5529, 2026-03-25 deployer cycle). Iteration 4 is a doc-only catch-up STATE-SYNC closing 9 metadata drift items (see `sessions/2026-05-16-s01.md`).

## Active Approach

None pending. The single `axiom erdos_1141_finitely_many` encodes the APSSV 2026 finiteness theorem (arXiv:2604.06609); it will become removable once Pollack's 2017 theorem on small prime quadratic residues is formalized in Mathlib.

## Blockers

- **External**: Pollack (2017) "Bounded gaps between primes in Chebotarev sets" / small-prime-quadratic-residues theorem not yet in Mathlib. Until then, the APSSV proof cannot be ported and the `erdos_1141_finitely_many` axiom remains a placeholder for the SOLVED-but-unformalized result.
- **None internal**: 0 sorries, build-verified.

## Next Action

Terminal phase. Available follow-ups for next claim cycle (not auto-actioned):

1. **a=2 variant**: define `IsErdos1141Good_a (a n : ℕ) : Prop` and verify some n with `n - 2k²` prime for all coprime k. APSSV proved finiteness for every fixed `a ≥ 1`; a per-`a` decidable predicate would enable computational study.
2. **OEIS A214583 search extension**: prove `¬ IsErdos1141Good n` for all `n ∈ [1723, 5000]` via `native_decide` (would extend the 41-known-good-values bound; current proof verifies the 41 are good but does not exclude intermediate values).
3. **Pollack theorem skeleton**: stub `theorem pollack_small_prime_quadratic_residue` in a companion `Erdos1141Pollack.lean` with the statement (`∀ ε > 0, ∀ q sufficiently large, ∀ a coprime to q, ∃ prime p ≤ q^{1/4+ε} with p ≡ a (mod q)`) and a `sorry`; then ship to Aristotle for proof search. Hard (requires deep analytic number theory) but well-scoped.

None of these are critical-path; slug is honestly "done" at the gallery-display level.

## Attempt Counts

- Total attempts: 1 (the original formalization in #5529)
- Current approach attempts: 0
- Approaches tried: 0

## Iteration History

| Iter | Date | Mode | Outcome | Key delta |
|------|------|------|---------|-----------|
| 1 | 2026-01-15 → 2026-03-25 | FRESH | initial formalization | created file, Decidable instance, 8 positive examples, 5 counterexamples, structural lemmas (PR #5381, #5529) |
| 2 | 2026-03-25 | FRESH | progress | added classification to n=100, unified `all_known_good`, structural corollaries (`good_not_prime_ge5`, `good_odd_eq_three`, `good_coprime3_sub9_prime`) |
| 3 | 2026-04-27 | REVISIT | completed | assessed and marked completed (`currentState.since` timestamp); axiom recognized as APSSV 2026 SOLVED placeholder |
| 4 | 2026-05-16 | REVISIT (catch-up) | doc-only STATE-SYNC | this session: closed 9 metadata drift items across 4 files, no Lean edit (see sessions/2026-05-16-s01.md) |

> PREP ≡ ORIENT in the skill-canonical phase taxonomy; this slug stays at COMPLETED across all sub-phases (catch-up cycles do not regress to ORIENT/ACT).
