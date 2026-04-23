# Selection Report: konigsberg-oq-02-oq-01

**Date**: 2026-04-23
**Seeker Session**: 2026-04-23
**Pool Status**: 32 available, 556 in-progress, 1405 completed

## Selected Problem

- **ID**: konigsberg-oq-02-oq-01
- **Name**: Hierholzer's Algorithm: Directed Eulerian Circuit Formalization in Lean 4
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Top composite score after diversity adjustment**: Composite 67 (EMPTY tier × -0 penalty + tractability 6×10 + significance 7). `triangle-angle-sum-oq-03` scored higher at 76 but was penalized: geometry domain recently selected (Minkowski), and degenerate angle API cases are shallow technical work rather than deep mathematics.
2. **Domain diversity**: Recent selections: Szemerédi regularity (combinatorics), Hölder/Cauchy-Schwarz (analysis), Minkowski (geometry). Graph theory/algorithms is a fresh domain — no recency penalty applies.
3. **EMPTY knowledge tier**: No prior research; OBSERVE phase starts with full discovery potential.
4. **Constructive proof with clear structure**: Hierholzer's algorithm has a well-defined termination argument (induction on remaining edges) that maps naturally to Lean 4's functional style.
5. **Gallery foundation available**: `konigsberg` (undirected case) is already in the gallery, providing `SimpleGraph`, degree theory, and walk infrastructure as templates.

## Rejection Summary

- **Candidates considered**: 32 available
- **Rejected (moonshots, tract≤2)**: twin-primes-special-oq-01, weak-goldbach-oq-01, sophie-germain-oq-01
- **Rejected (low tractability, tract=3)**: szemeredi-full-oq-02
- **Rejected (diversity penalty — geometry)**: triangle-angle-sum-oq-03 (highest raw score 76, penalized — geometry domain, recent Minkowski selection)
- **Rejected (recently selected)**: szemeredi-regularity-oq-02, cauchy-schwarz-integral-oq-01-oq-03-oq-01
- **Runners-up** (composite 67 each): erdos-268-incomplete-01 (number theory), erdos-476-oq-05-wip-01 (additive combinatorics), newton-inductive-step-oq-03 (algebra)
- **Tie-breaking**: Among equal-scoring candidates, graph theory/algorithms selected for maximal domain diversity relative to recent pipeline
- **Confidence**: high (clear domain gap, constructive algorithm, existing gallery infrastructure)

## Related Gallery Proofs

- `konigsberg`: Undirected Eulerian circuit — direct predecessor proof, provides SimpleGraph walk infrastructure
- `konigsberg-oq-02`: Directed graph degree characterization — sister problem

## Suggested First Steps

1. **OBSERVE**: Survey `Mathlib.Combinatorics.SimpleGraph.Euler` and check for any directed graph Eulerian lemmas; inspect `Quiver` API for directed graph support
2. **ORIENT**: Study `konigsberg` gallery proof structure; identify which undirected lemmas transfer vs. need directed equivalents
3. **DECIDE**: Choose approach — constructive Hierholzer algorithm (greedy cycle extension + merge) vs. induction on edge count; assess Mathlib directed graph types

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 32 |
| In Progress | 556 |
| Completed | 1405 |
| Graduated | 8 |
| Blocked | 3 |

## Candidate Pool Health

- Pool depth: **adequate** (32 available >> 15 threshold)
- Domain distribution: good coverage across algebra, analysis, combinatorics, graph theory, number theory
- Next refresh recommended: 30 minutes (standard interval)

## Initialized

- [x] Research workspace created: `research/problems/konigsberg-oq-02-oq-01/`
- [x] problem.md populated with mathematical context and proof approaches
- [x] knowledge.md initialized
- [x] state.md set to OBSERVE phase
- [x] Registered in database with status 'available'
- [x] Pool synced
- [ ] Ready for /researcher
