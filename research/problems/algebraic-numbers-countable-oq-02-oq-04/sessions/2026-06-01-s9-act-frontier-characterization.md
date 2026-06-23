# S9 ACT — Boundary characterization: every real is a boundary point

**Date**: 2026-06-01
**Researcher**: researcher-1
**Phase**: S9 ACT (Boundary / frontier characterization)
**Base SHA**: `f486a19e2e0` (`origin/main`)
**Branch**: `research/algebraic-numbers-countable-oq02oq04-s1-2026-06-01`
**Status**: Docker `✔ 3067/3067 jobs`, 10s file compile.

## Summary

S7 (closure = univ) and S8 (interior = ∅) together pin down the topological
boundary of the computable/non-computable partition exactly: every real is a
boundary point of *both* sides. Two new one-line theorems realise this:

```
frontier_computable_reals_eq_univ    : frontier {r | IsComputable r} = Set.univ
frontier_nonComputableReals_eq_univ  : frontier nonComputableReals     = Set.univ
```

Proof: `frontier s := closure s \ interior s`, so combining
`closure_computable_reals_eq_univ` (S7) with `interior_computable_reals_eq_empty`
(S8 corollary) collapses the goal to `univ \ ∅ = univ`, discharged by
`Set.diff_empty`. Symmetric on the non-computable side.

## Mathematical content

The topological profile of the partition `ℝ = {computable} ⊔ {non-computable}`
is now complete on both sides:

| Side             | Cardinality | Density | Interior | Closure | Frontier | Baire category |
|------------------|-------------|---------|----------|---------|----------|----------------|
| computable       | ℵ₀ (S3)     | dense (S7) | ∅ (S8 cor)  | univ (S7)  | **univ (S9)**  | meagre (S8)    |
| non-computable   | 𝔠 (S4)     | dense (S8-prep) | ∅ (S8 cor)  | univ (S8-prep) | **univ (S9)** | residual (S8)  |

No real lies in the interior of either side: every real is approached from
*both* the computable side (S7) *and* the non-computable side (S8-prep)
simultaneously. The two-sided accumulation profile is the same one carried by
the rational/irrational partition of `ℝ`, refined here to the strictly finer
computable/non-computable split.

## Diff

```
proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean: 869 → 928 LOC (+59)
  - 1 new docstring section (S9 boundary characterization)
  - 2 new theorems (frontier_*_eq_univ)
  - 0 new definitions
  - 0 new sorries
  - 0 new axioms
  - 0 new imports
src/data/proofs/algebraic-numbers-countable-oq-02-oq-04/meta.json:
  - lineCount: 869 → 928 (both occurrences)
  - leanFiles[0].theoremCount: 40 → 42 (top-level remains stale at 31, awaiting
    a separate mechanic count-sync pass per the S6f memo)
```

No `proofs/Proofs.lean` change (file already registered).

## Mathlib API used

Two stock identities, both already transitively available via the existing
`Mathlib.Tactic` / topology import chain — no new imports added:

- `frontier` (definition, `Mathlib.Topology.Basic`) — `frontier s := closure s \ interior s`.
- `Set.diff_empty` — `s \ ∅ = s`.

The proofs reuse only locally-proved lemmas from S7 / S8-prep / S8.

## Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.AlgebraicNumbersCountableOQ02OQ04
Build completed successfully (3067 jobs).
=== Build succeeded ===

✔ [3067/3067] Built Proofs.AlgebraicNumbersCountableOQ02OQ04 (10s)
```

## What's next (S10+)

The Baire-category / topological track is now closed: cardinality (S3, S4),
density (S7, S8-prep), category (S8), interior/closure/frontier (S8, S9).
Remaining headline targets:

1. **`IsComputable e` (or `π`)** — explicit computable transcendental witness
   sharpening `algebraic ⊊ computable` beyond pure cardinality + topology.
   Status: still blocked on Mathlib gap (no `Computable.add` / `Computable.neg`
   on `ℚ` at v4.26.0). See state.md S6f §5 priority tree.
2. **Explicit non-computable real** — e.g. Chaitin's Ω, a halting-encoding
   diagonal, or a Specker sequence. Pure-cardinality existence is already
   recorded as `exists_non_computable_real` (S4); an *explicit* witness would
   convert that into a constructive statement.
3. **`algebraic ⊆ computable`** — every algebraic real is computable via
   root-finding (Sturm + bisection). Requires substantial Mathlib computability
   API not yet present (computable arithmetic, computable sign-changes).

## Status updates

- `state.md`: Phase advanced S8 → S9. Inventory snapshot updated to 928 LOC,
  42 theorems, 3 defs, 0 sorries, 0 axioms. Build status remains
  `✔ 3067/3067` Docker-verified.
- `meta.json`: `lineCount` 869 → 928 (both occurrences); leanFiles[0]
  `theoremCount` 40 → 42.
- `currentState.json` / `aristotle-jobs.json`: untouched (no Aristotle interaction).

## Knowledge score delta

Pre-S9 knowledge score: 51 (RICH). Post-S9 (this PR): expected +2-3 for the
two new theorems + topology section. No new axioms, no new sorries, no new
definitions, no new imports.
