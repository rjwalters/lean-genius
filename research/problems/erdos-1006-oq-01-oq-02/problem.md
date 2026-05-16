# Problem: Cover Graph Recognition in P?

**ID**: erdos-1006-oq-01-oq-02
**Category**: open-question (Erdős #1006 sub-question)
**Tractability**: 5/10
**Significance**: 6/10
**Source Proof**: erdos-1006 (parent gallery entry)
**Tags**: erdos, graph-theory, complexity, posets, cover-graphs, np

## Problem Statement

Can cover graph recognition (deciding if a graph is the Hasse diagram of some finite poset) be done in polynomial time?

## Context

A *cover graph* (also called Hasse graph) is the undirected graph
underlying the Hasse diagram of a finite poset: vertices are the
poset elements, and edges are exactly the covering relations
(`a ⋖ b` iff `a < b` and there is no `c` with `a < c < b`).

The recognition problem is: given a simple undirected graph `G`, does
there exist a finite poset `P` whose cover graph (Hasse diagram) is
exactly `G`? The decision version is in NP (the poset is a polynomial
certificate), but its membership in P is an open question in
combinatorics / computational complexity.

This slug is a Lean formalization of the surrounding lattice and the
strict separation between cover graphs and comparability graphs. The
file `Erdos1006OQ01OQ02.lean` axiomatizes the open question as
`cover_graph_recognition_in_p` and develops the supporting infrastructure
including a K₃ strict-separation witness (K₃ is a comparability graph
but not a cover graph).

## Lean Formalization Status

As of 2026-05-16 (S1 OBSERVE bootstrap):

- `proofs/Proofs/Erdos1006OQ01OQ02.lean` — 256 LOC, 9 theorems/lemmas,
  2 axioms, 4 definitions, 0 sorries.
- The 2 axioms are:
  1. `comparability_recognition_in_p` — known to be in P (Golumbic; stated as axiom for compactness).
  2. `cover_graph_recognition_in_p` — **the open question**, stated as
     an axiom so the file type-checks while the mathematical question
     remains open.
- The file establishes strict separation:
  `cover_subclass_comparability` + `cover_strictly_subset_comparability` (K₃ witness).
- Build status: not directly verified in this slug's session log
  (parent gallery `erdos-1006` is the build-bearing slug).

## Research Phase

OBSERVE (S1, 2026-05-16, researcher-3 bootstrap). No prior state.md
existed; this PR creates the slug infrastructure (state.md, problem.md,
sessions/, JSON `currentState`).

## Key Questions

1. Is `cover_graph_recognition_in_p` actually open, or has it been
   resolved upstream since the slug's last activity (2026-05-03,
   PR #15112)?
2. Are there partial results (sub-classes solvable in P, e.g.,
   bounded-width, planar, etc.) that could be formalized to reduce the
   strength of the axiom?
3. Should the file's `cover_subclass_comparability` line be hardened
   into a reusable Mathlib contribution (cover graphs are a
   strict sub-class of comparability graphs)?

## Related Slugs

- `erdos-1006` (parent gallery)
- `erdos-1006-oq-01` (parent OQ-01: cover graph axiomatization)
- `erdos-1006-oq-01-oq-01` (sibling: Pretzel characterization formalization without axioms)

## References

- Erdős Problem #1006 (graph-theoretic open question collection)
- Brightwell & West, "Partially Ordered Sets" (cover graphs background)
- Pretzel, "Robustly acyclic orientations and cover graphs" (proof
  technique referenced in `erdos-1006-oq-01-oq-01`)
- Golumbic, "Algorithmic Graph Theory and Perfect Graphs" (comparability
  graph recognition in P)
