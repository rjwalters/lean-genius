# Research State: erdos-85-wip-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-07-09T17:33:20-07:00
**Iteration**: 1

## Current Focus
Initial problem understanding. Read problem.md and gather context.

## Active Approach
None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.

## Status (researcher-1, 2026-07-23) — abstract surgery engine + f(13) ≥ 4

(The template header above predates the real work — see knowledge.md for the full
session history; the exact table f(1..12) is complete on main.)

This session: the vertex-adding surgery is now an ABSTRACT lemma set in
`Erdos85Problem.lean` (section Surgery): `surgery G a b c : SimpleGraph (Option V)`
with degree preservation, common-neighbour ≤ 1 preservation (hypotheses: a~b, b~c,
a≁c, a≠c, edges ab/bc triangle-free), generic `four_le_minDegreeForC4_of_witness`,
and `finSuccEquiv` transport. Applied to petersen12 (a=4, b=9, c=7):
**f(13) ≥ 4**, hence f(13) ∈ {4,5} (`minDegreeForC4_thirteen_mem`) — first rung
beyond the counting range, no 13-vertex decide.

## Status (researcher-2, 2026-07-24) — **f(13) = 4 PROVED** (friendship theorem)

The f(13) ≤ 4 blocker is RESOLVED by a materially new mechanism — not a Reiman
edge bound, but equality analysis of the cherry count at the projective-plane
parameter point 13 = 4·3+1 (`13·C(4,2) = C(13,2) = 78` exactly): tightness forces
4-regularity + surjectivity of the cherry→endpoint-pair map, i.e. the friendship
condition, and `Theorems100.friendship_theorem` (Mathlib Archive, importable in
this toolchain!) yields a degree-12 politician — contradiction with 4-regularity.
`minDegreeForC4_thirteen : minDegreeForC4 13 = 4` — exact table now 1..13.
0 sorries, 0 axioms. See knowledge.md session 2026-07-24.

## Blockers
- Upper bounds beyond n = 13: the friendship mechanism is SPECIFIC to the tight
  points n = k²−k+1 (generalization f(k²−k+1) ≤ k is a candidate target); other
  n still need real ex(n;C₄) edge-extremal input. Reopen: formalize a
  Reiman-type bound.
- General ∀ n ≥ 10 f(n) ≥ 4: needs config EXISTENCE (edge pair ab, bc both
  triangle-free, a≁c) in iterated witnesses — not automatic in arbitrary
  C₄-free min-deg-3 graphs. Reopen: invariant-maintaining induction or
  disjoint-union route (needs base cases 13..19 + graph-sum infrastructure).
- Deep: KST asymptotics; monotonicity core (the actual Erdős #85) OPEN.
