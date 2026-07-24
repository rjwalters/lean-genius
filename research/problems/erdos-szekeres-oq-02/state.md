# Research State: erdos-szekeres-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-24T00:00:00-07:00
**Iteration**: 5
**Last Updated**: 2026-07-24 (S5, researcher-1 — UNBLOCKED, milestone 1 + realized-witness layer landed)

## Session 5 (2026-07-24, researcher-1) — UNBLOCK + FIRST LEAN ARTIFACT

The 2026-06-13/14 BLOCKED flag was Docker-transient by its own terms ("un-block
the moment Docker is back"). Docker is back; `claim-random` served the slug and
ACT proceeded. Landed `proofs/Proofs/ErdosSzekeresOQ02.lean` (319 LOC, 0 sorry,
0 axiom, Docker build 8577 jobs clean): computable `incDP` + recurrence +
bounds; `ExactIncEnd` invariant + snoc extension; `exactIncEnd_incDP` (DP value
realized); `hasIncreasingEndingAt_incDP`; `incDP_le_maxIncLen` (constructive
half of correctness, obtained WITHOUT oq-01's extension lemma);
`exists_increasingSubseq_incDP`; exact cost layer `incDPcost n = n(n-1)/2`
(+ division-free form), grounded as scanned-pair count. Milestone 1 COMPLETE;
milestone 2 half done.

## Current Focus
Milestone 2 remaining half: `maxIncLen f i ≤ incDP f i` via the stripping /
optimal-substructure lemma (exact statement in knowledge.md §Remaining gaps —
downward handling of the parent disjunction's weak branch; does NOT need
oq-01's `maxIncLen_lt_of_lt` after all). Then milestone 3: computable
`incWitness` via `List.argmax` predecessor selection (design pinned in
knowledge.md). Statement pinning now lives in problem.md ("Must prove exactly /
does not count").

## Active Approach
Computable DP `incDP` (landed) shown sound against the parent's noncomputable
`maxIncLen` (landed); completeness (≥) via stripping; witness as executable
data via argmax backtracking. Θ(n log n) patience sorting + Fredman Ω(n log n)
remain literature-only (no comparison-cost model in Mathlib) — documented in
the file header, out of Lean scope by design.
